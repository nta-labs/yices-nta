/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */
 
#ifndef NA_PLUGIN_H_
#define NA_PLUGIN_H_

#include "mcsat/plugin.h"
#include "mcsat/nta_info.h"

/** Allocate a new na plugin and setup the plugin-interface method */
plugin_t* na_plugin_allocator(void);

/** Set the nta_info pointer in the NA plugin */
void na_plugin_set_nta_info(plugin_t* plugin, nta_info_t* nta_info);

#endif /* NA_PLUGIN_H_ */
