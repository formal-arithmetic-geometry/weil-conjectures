/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import WeilConjectures.CategoryTheory.CartanEilenbergRowsExists
import WeilConjectures.CategoryTheory.CartanEilenbergRowsIdentifications

/-! # Existence of Cartan--Eilenberg injective resolutions

Source: Stacks Project, derived.tex, Definition 015H and Lemma 015I
(blueprint: lem-sp-cartan-eilenberg-exists).

The resolution index is natural, equivalently extending by zero in negative degrees.
The augmentation is a morphism of bicomplexes from the complex placed in vertical
degree zero. Kernels, images and homology in the category of vertical complexes
are computed degreewise. Quasi-isomorphisms from these single-degree complexes,
together with injectivity of every target term, express injective resolutions
using exactly the data of `CategoryTheory.InjectiveResolution`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe u v

end CategoryTheory
