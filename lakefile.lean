/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import Lake
open Lake DSL

package FeffermanClayNS where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0-rc1"

@[default_target]
lean_lib FeffermanClayNS where
  roots := #[`FeffermanClayNS]
  globs := #[
    .one `FeffermanClayNS,
    .submodules `FeffermanClayNS
  ]

set_option linter.unusedVariables false
