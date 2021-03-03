/*
 * Copyright (c) 2019-2020 Dogan Ulus
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

#pragma once

#include <memory>
#include <vector>

#include "reelay/common.hpp"
#include "reelay/networks/basic_structure.hpp"
#include "reelay/unordered_data.hpp"

namespace reelay {
namespace discrete_timed_data_setting {

template <typename X, typename T>
struct disjunction final : public discrete_timed_node<data_set_t, T> {
  using time_t = T;
  using input_t = X;
  using value_t = data_set_t;
  using output_t = data_set_t;

  using node_t = discrete_timed_node<output_t, time_t>;
  using state_t = discrete_timed_state<input_t, output_t, time_t>;

  using node_ptr_t = std::shared_ptr<node_t>;
  using state_ptr_t = std::shared_ptr<state_t>;

  std::vector<node_ptr_t> args;

  explicit disjunction(const std::vector<node_ptr_t> &nodeptrs)
      : args(nodeptrs) {}

  explicit disjunction(const kwargs &kw)
      : disjunction(reelay::any_cast<std::vector<node_ptr_t>>(kw.at("args"))) {}

  output_t output(time_t now) {
    output_t result = args[0]->output(now);
    for (size_t i = 1; i < args.size(); i++) {
      result += args[i]->output(now);
    }
    return result;
  }
};

} // namespace discrete_timed_robustness_setting
}  // namespace reelay