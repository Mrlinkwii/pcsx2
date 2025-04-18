// SPDX-FileCopyrightText: 2002-2025 PCSX2 Dev Team
// SPDX-License-Identifier: GPL-3.0+

#pragma once

#include "ThreadedFileReader.h"
#include <zlib.h>

struct CsoHeader;

class CsoFileReader final : public ThreadedFileReader
{
	DeclareNoncopyableObject(CsoFileReader);

public:
	CsoFileReader();
	~CsoFileReader() override;

	bool Open2(std::string filename, Error* error) override;

	bool Precache2(ProgressCallback* progress, Error* error) override;

	Chunk ChunkForOffset(u64 offset) override;
	int ReadChunk(void* dst, s64 chunkID) override;

	void Close2() override;

	u32 GetBlockCount() const override;

private:
	static bool ValidateHeader(const CsoHeader& hdr, Error* error);
	bool ReadFileHeader(Error* error);
	bool InitializeBuffers(Error* error);
	int ReadFromFrame(u8* dest, u64 pos, int maxBytes);
	bool DecompressFrame(Bytef* dst, u32 frame, u32 readBufferSize);
	bool DecompressFrame(u32 frame, u32 readBufferSize);

	u32 m_frameSize = 0;
	u8 m_frameShift = 0;
	u8 m_indexShift = 0;
	bool m_uselz4 = false; // flag to enable LZ4 decompression (ZSO files)
	std::unique_ptr<u8[]> m_readBuffer;

	std::unique_ptr<u32[]> m_index;
	u64 m_totalSize = 0;
	// The actual source cso file handle.
	std::FILE* m_src = nullptr;
	std::unique_ptr<u8[]> m_file_cache;
	size_t m_file_cache_size = 0;
	z_stream m_z_stream = {};
};
