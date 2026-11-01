/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.TraceFormulaCoefficientSetup
public import WeilConjectures.SixFunctors.Supporting.SixFunctorOperationDatumStages
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImageSupplement

/-! # Direct-image closure of the finite geometric domain

Source: latest blueprint thm-sf-ctf-stability (iii), cor-sf-direct-image-ctf-proetale.
(blueprint: lem-trf-finite-geometric-direct-domain).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The recorded ordinary direct image preserves the finite-Tor domain over the field.
Source: latest blueprint thm-sf-ctf-stability (iii), cor-sf-direct-image-ctf-proetale
(blueprint: lem-trf-finite-geometric-direct-domain).

Proof: finite type over the field bounds the source dimension by d, including the empty
source. The finite direct-image theorem sends the input Tor interval [a,b] to [a,b+2d]
and proves bounded constructibility of the same output. These two conclusions are
exactly membership in the finite-Tor domain. -/
theorem finiteGeometricDirect_domain
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ)
    (X Y : SixFunctorSpace D) (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (K : proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing l E (n + 1)))
    (hK : finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X.obj.left K) :
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) Y.obj.left
      ((proEtaleConstantDerivedDirectImage f.hom.left
        (Padic.coefficientExtensionRing l E (n + 1))).obj K) := by
  let : LocallyOfFiniteType X.obj.hom := X.property.1
  let : QuasiCompact X.obj.hom := X.property.2
  let : LocallyOfFiniteType Y.obj.hom := Y.property.1
  let : QuasiCompact Y.obj.hom := Y.property.2
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le X.obj.hom
  obtain ⟨a, b, ht⟩ := hK.2
  obtain ⟨hc, ht'⟩ := ProEtale.finiteCoefficientDirectImage_boundedConstructible_torAmplitude
    D l hl E (n + 1) (Nat.succ_pos n) X.obj Y.obj f.hom d hd a b hK ht
  exact ⟨hc, a, b + 2 * (d : ℤ), ht'⟩

end WeilConjectures
