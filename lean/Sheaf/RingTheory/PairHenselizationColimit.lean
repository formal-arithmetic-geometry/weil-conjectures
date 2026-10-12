/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian

import Sheaf.RingTheory.PairHenselizationEssentiallySmall
import Sheaf.RingTheory.PairHenselizationFiltered
import Sheaf.AlgebraicGeometry.EtaleAlgebraFilteredColimitDescent
import Sheaf.RingTheory.EtaleSectionIdempotentSplitting
import Sheaf.RingTheory.HenselianOfEtaleSectionLifting

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

/-- A henselian colimit with unchanged quotient for the etale neighbourhood category.
Source: Stacks Project, Tag 0A02, colimit and section-lifting paragraphs.
(blueprint: lem-weil-pbc-pair-henselization-colimit).

Proof: Use essential smallness and filteredness to pass to a small equivalent category.
Form its filtered colimit H of B-algebras and transport the cocone and its universal
property back to the full category. The vertex is an object of the under category.
For each object C there is a unique B-algebra map pi_C : C to R = B/J: factor through
C/JC and invert the given quotient isomorphism. Uniqueness makes these maps compatible.
They induce pi : H to R, killing JH. On quotients this is a left inverse of R to H/JH.
Every element of H comes from some C, and modulo JC is the image of an element of B;
therefore R to H/JH is also surjective and is an isomorphism.
To prove henselianness, take an etale H-algebra A and an H-algebra section A to H/JH.
Etale filtered-colimit descent gives a stage C and an etale C-algebra D with
A isomorphic to H tensor_C D. The section and H/JH isomorphic to R give s : D to R.
Over R the etale algebra D/JD has this section. Idempotent splitting gives an idempotent
e in D/JD whose localization is R and whose image under s is 1. Lift e to g in D.
Then D localized at g is etale over B and has quotient R, hence is an object of the
original category. Its coprojection to H agrees on C with the original coprojection.
The tensor universal property now gives an H-algebra map A to H. Its reduction is the
chosen section: s extends to the localization since s(g)=1, and this extension equals
the unique map pi for that object. Thus all etale sections lift. Apply
`henselianRing_of_etale_section_lifting` (Stacks 09XI) to get HenselianRing H (JH).
The colimit and quotient arguments above supply the other asserted conjuncts. -/
theorem pair_henselization_colimit (B : Type u) [CommRing B] (J : Ideal B) :
    ∃ c : Cocone (ObjectProperty.ι
      (fun C : Under (CommRingCat.of B) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
            (Ideal.le_comap_map)))),
      Nonempty (IsColimit c) ∧
        HenselianRing c.pt.right (J.map c.pt.hom.hom) ∧
        Function.Bijective (Ideal.quotientMap (J.map c.pt.hom.hom) c.pt.hom.hom
          (Ideal.le_comap_map)) := by
  sorry

end RingTheory
