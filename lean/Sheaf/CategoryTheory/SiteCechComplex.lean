/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.SiteCechComplex

/-!
# Čech complexes of coverings on a site

Source: Stacks Project, Cohomology on Sites, Tags 03AK, 03AM, 03AO, 03AQ
(blueprint: def-weil-pbc-site-cech-complex).

`SiteCechComplex` records the chosen fibre products, including their universal properties.
Its `complexFunctor` constructs the alternating restriction complex; `cohomologyFunctor`
is its cohomology. Only verification proofs are postponed, never the differential or maps.
-/
