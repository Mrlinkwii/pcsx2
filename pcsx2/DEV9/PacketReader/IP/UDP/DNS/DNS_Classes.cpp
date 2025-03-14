// SPDX-FileCopyrightText: 2002-2025 PCSX2 Dev Team
// SPDX-License-Identifier: GPL-3.0+

#include "DNS_Classes.h"
#include "DEV9/PacketReader/NetLib.h"

namespace PacketReader::IP::UDP::DNS
{
	DNS_QuestionEntry::DNS_QuestionEntry(const std::string& qName, u16 qType, u16 qClass)
		: name{qName}
		, entryType{qType}
		, entryClass{qClass}
	{
	}
	DNS_QuestionEntry::DNS_QuestionEntry(const u8* buffer, int* offset)
	{
		ReadDNS_String(buffer, offset, &name);
		NetLib::ReadUInt16(buffer, offset, &entryType);
		NetLib::ReadUInt16(buffer, offset, &entryClass);
	}

	void DNS_QuestionEntry::ReadDNS_String(const u8* buffer, int* offset, std::string* value) const
	{
		*value = "";

		while (buffer[*offset] != 0)
		{
			const int len = buffer[*offset];

			if (len >= 192)
			{
				//len instead contains a pointer to the rest of the string
				u8 addrB[2];
				NetLib::ReadByteArray(buffer, offset, 2, addrB);

				addrB[0] &= ~0xC0;
				u16 addr;
				int tmp = 0;
				NetLib::ReadUInt16(addrB, &tmp, &addr);
				tmp = addr;
				std::string o;
				ReadDNS_String(buffer, &tmp, &o);
				*value += o;
				//Ends with the pointer, no null char
				return;
			}
			else
			{
				*offset += 1;
				*value += std::string((char*)&buffer[*offset], len);
				*offset += len;

				if (buffer[*offset] != 0)
					*value += ".";
			}
		}
		//null char
		*offset += 1;
	}
	void DNS_QuestionEntry::WriteDNS_String(u8* buffer, int* offset, const std::string& value) const
	{
		int segmentLength = 0;
		int segmentStart = 0;
		for (size_t i = 0; i < value.size(); i++)
		{
			if (value[i] == '.')
			{
				if (segmentLength == 0)
					continue;

				NetLib::WriteByte08(buffer, offset, segmentLength);
				NetLib::WriteByteArray(buffer, offset, segmentLength, (u8*)&value.c_str()[segmentStart]);
				segmentLength = 0;
				segmentStart = i + 1;
			}
			else
				segmentLength++;
			continue;
		}
		if (segmentLength != 0)
		{
			NetLib::WriteByte08(buffer, offset, segmentLength);
			NetLib::WriteByteArray(buffer, offset, segmentLength, (u8*)&value.c_str()[segmentStart]);
		}
		//null char
		NetLib::WriteByte08(buffer, offset, 0);
	}

	int DNS_QuestionEntry::GetLength() const
	{
		return 1 + name.size() + 1 + 4;
	}

	void DNS_QuestionEntry::WriteBytes(u8* buffer, int* offset) const
	{
		WriteDNS_String(buffer, offset, name);
		NetLib::WriteUInt16(buffer, offset, entryType);
		NetLib::WriteUInt16(buffer, offset, entryClass);
	}

	DNS_ResponseEntry::DNS_ResponseEntry(const std::string& rName, u16 rType, u16 rClass, const std::vector<u8>& rData, u32 rTTL)
		: DNS_QuestionEntry(rName, rType, rClass)
		, timeToLive{rTTL}
		, data{rData}
	{
	}

	DNS_ResponseEntry::DNS_ResponseEntry(const u8* buffer, int* offset)
		: DNS_QuestionEntry(buffer, offset)
	{
		u16 dataLen;
		NetLib::ReadUInt32(buffer, offset, &timeToLive);
		NetLib::ReadUInt16(buffer, offset, &dataLen);

		data = {&buffer[*offset], &buffer[*offset + dataLen]};
		*offset += dataLen;
	}

	int DNS_ResponseEntry::GetLength() const
	{
		return DNS_QuestionEntry::GetLength() + 4 + 2 + data.size();
	}

	void DNS_ResponseEntry::WriteBytes(u8* buffer, int* offset) const
	{
		DNS_QuestionEntry::WriteBytes(buffer, offset);
		NetLib::WriteUInt32(buffer, offset, timeToLive);
		NetLib::WriteUInt16(buffer, offset, data.size());
		NetLib::WriteByteArray(buffer, offset, data.size(), &data[0]);
	}
} // namespace PacketReader::IP::UDP::DNS
