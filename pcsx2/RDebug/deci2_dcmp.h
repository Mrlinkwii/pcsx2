// SPDX-FileCopyrightText: 2002-2025 PCSX2 Dev Team
// SPDX-License-Identifier: GPL-3.0+

#pragma once

#include "Common.h"
#include "deci2.h"

void D2_DCMP(const u8 *inbuffer, u8 *outbuffer, char *message);
void sendDCMP(u16 protocol, u8 source, u8 destination, u8 type, u8 code, char *data, int size);
