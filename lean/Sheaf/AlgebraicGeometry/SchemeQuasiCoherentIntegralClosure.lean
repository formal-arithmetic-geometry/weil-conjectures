module

public import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Algebra.Module.LocalizedModule.Basic
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-!
# Stalkwise integral closure of a quasi-coherent algebra on a scheme

Source: Stacks Project, Morphisms, Tag 035F, lemma-integral-closure
(blueprint: lem-sfb-scheme-quasicoherent-integral-closure).

The subalgebra is specified by an inclusion whose section images are precisely the
stalkwise integral sections. Its stalk and affine section images are integral closures
through the given structure morphism, rather than abstractly isomorphic algebras.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- The stalkwise integral sections form a quasi-coherent subalgebra, with the expected
stalks and affine sections. No separation, finiteness or reducedness hypothesis is needed.
Source: Stacks Project, Morphisms, Tag 035F, lemma-integral-closure
(blueprint: lem-sfb-scheme-quasicoherent-integral-closure).

Proof:
1. Restriction preserves integral germs. Compatible sections glue in the ambient algebra,
and their germs remain integral, so the condition defines a subsheaf. Integral elements
form a subring containing scalars (def-weil-pbc-integral-closure); hence this is a subalgebra.
2. On an affine open Spec R the tilde-Gamma adjunction identifies the ambient module with
the tilde of its section algebra A (lem-weil-pbc-affine-tilde-gamma-adjunction). Principal
open sections and stalks are the corresponding localizations (lem-weil-pbc-spec-module-
tilde-sections and lem-weil-pbc-spec-tilde-stalk-localization). The identifications preserve
multiplication, as seen on fractions. The prime-local criterion for integrality
(lem-sfb-integral-element-prime-local-criterion) therefore identifies these sections with
the integral closure C of R in A.
3. Integral closure commutes with localization (lem-weil-pbc-integral-closure-commutes-
localization), so the sections on D(f) are C_f. Clearing denominators extends every section
after multiplication by a power of f; the localization equality criterion kills sections
vanishing on D(f) by a power of f (def-weil-pbc-module-localization). Apply
pqf-lem-qcoh-principal-open-criterion to obtain quasi-coherence.
4. The stalk inclusion is injective by the equality criterion for germs
(def-weil-pbc-module-stalk). Its image consists of integral elements by construction.
Conversely, on an affine neighbourhood an integral stalk element is c/s with c in C and
s outside the prime, by integral-closure localization. The section c belongs to the
subalgebra by step 2, and multiplying by the inverse of s on D(s) represents the prescribed
germ in the subalgebra. This gives exactly the stated stalk image. -/
theorem exists_quasiCoherent_stalkwiseIntegralClosure
    (Y : Scheme.{u}) (B : Y.CommAlgebraSheaf)
    (hB : Y.IsQuasiCoherentAlgebra B) :
    ∃ (D : Y.CommAlgebraSheaf) (ι : D ⟶ B),
      Y.IsQuasiCoherentAlgebra D ∧
      (∀ V : Y.Opens, Function.Injective (ι.right.hom.app (op V))) ∧
      (∀ (V : Y.Opens) (b : B.right.obj.obj (op V)),
        b ∈ Set.range (ι.right.hom.app (op V)) ↔
          ∀ (y : Y) (hy : y ∈ V),
            ((TopCat.Presheaf.stalkFunctor CommRingCat y).map B.hom.hom).hom.IsIntegralElem
              (TopCat.Presheaf.germ (C := CommRingCat) B.right.obj V y hy b)) ∧
      (∀ y : Y,
        Function.Injective
          ((TopCat.Presheaf.stalkFunctor CommRingCat y).map ι.right.hom) ∧
        ∀ b : (TopCat.Presheaf.stalkFunctor CommRingCat y).obj B.right.obj,
          b ∈ Set.range ((TopCat.Presheaf.stalkFunctor CommRingCat y).map ι.right.hom) ↔
            ((TopCat.Presheaf.stalkFunctor CommRingCat y).map B.hom.hom).hom.IsIntegralElem
              b) ∧
      (∀ (V : Y.Opens), IsAffineOpen V → ∀ b : B.right.obj.obj (op V),
        b ∈ Set.range (ι.right.hom.app (op V)) ↔
          (B.hom.hom.app (op V)).hom.IsIntegralElem b) := by
  sorry

end AlgebraicGeometry.Scheme
