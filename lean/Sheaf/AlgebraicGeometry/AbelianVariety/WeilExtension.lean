/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.IsRegularScheme
import Sheaf.TraceFormula.SmoothGeometricallyNormal
import Sheaf.AlgebraicGeometry.RationalMapExtensionValuationPoint
import Sheaf.AlgebraicGeometry.GroupRationalDivisorialIndeterminacy

/-!
# Weil extension to an abelian variety

Source: Milne, Algebraic Groups (2017), 8.18, printed p.152, combining 8.16 and 8.17;
Milne, Abelian Varieties, Chapter I, Theorems 3.1–3.2 and Lemma 3.3, printed pp.16–18.
(blueprint: lem-sfb-weil-extension-to-abelian-variety).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A morphism over `k` from a dense open of a smooth integral separated finite-type
`k`-scheme to an abelian variety extends uniquely to the entire source.

Source: Milne, Algebraic Groups (2017), 8.18, printed p.152 (combine 8.16 and 8.17);
Milne, Abelian Varieties I, Theorems 3.1–3.2 and Lemma 3.3, printed pp.16–18.
(blueprint: lem-sfb-weil-extension-to-abelian-variety).

Proof following the five steps of the node:
1. Apply lem-trf-smooth-geometrically-normal with the identity extension: X is regular
   and its stalks are normal domains. By def-weil-regular-scheme and finite type,
   X is locally Noetherian and quasi-compact, hence Noetherian. It is reduced and
   irreducible by def-pc-integral-scheme. By def-sc-abelian-variety and
   def-weil-proper-morphism, B is smooth, connected, proper, separated and finite type.
2. Let D be the union of all open domains containing U to which f extends over k.
   Two extensions agree on their intersection: U is dense there, the intersection
   is reduced by def-pc-reduced-scheme, and lem-sfb-relative-separated-dominant-ext
   applies to the separated target over k. By lem-weil-pbc-scheme-morphism-gluing
   they glue to F_D. Uniqueness of gluing shows F_D is over k and restricts to f.
3. Every point x whose local ring has dimension one has a DVR stalk, by
   lem-sc-normal-dim1-dvr and step 1. It is a valuation ring by
   def-sc-discrete-valuation-ring. By lem-sfb-rational-map-extension-valuation-point,
   f extends to an open containing both U and x. Thus x belongs to D.
4. Apply lem-sfb-group-rational-divisorial-indeterminacy to X, B, U, f and D.
   If D is not all of X, its complement has a nonempty finite family of irreducible
   closed components with generic stalk dimension one. Any such generic point
   contradicts step 3. Hence D=X and F_D gives the required extension.
5. Two extensions agree on the dense open U. Since X is reduced and B is separated
   over k, lem-sfb-relative-separated-dominant-ext makes them equal on X. -/
theorem existsUnique_extension_to_abelianVariety
    (k : Type u) [Field k]
    (X : Over (Spec (.of k))) [IsIntegral X.left]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [Smooth X.hom]
    (B : Over (Spec (.of k))) [GrpObj B] [IsAbelianVariety B]
    (U : X.left.Opens) (hU : Dense (U : Set X.left))
    (f : U.toScheme ⟶ B.left) (hf : f ≫ B.hom = U.ι ≫ X.hom) :
    ∃! F : X.left ⟶ B.left, F ≫ B.hom = X.hom ∧ U.ι ≫ F = f := by
  sorry

end AlgebraicGeometry
