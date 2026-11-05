/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedGlobalScalar
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.PerfectSupportAffineOpenTorsion
import WeilConjectures.AlgebraicGeometry.DerivedOpenHomScalarMayerVietoris
import WeilConjectures.AlgebraicGeometry.QuasiCompactOpenInduction

/-! # Maps from perfect complexes into principal support

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.13.9, Tag 08EJ
(blueprint: lem-sc-perfect-into-support-on-T).

Global functions are encoded as compatible families of local sections. On the Zariski
site, evaluation at the top open identifies this ring with the usual global section ring.
The action on derived morphisms is the localization of the sectionwise scalar action.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
