/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A8
-/
module

public import Sheaf.Paper.PointDerivedHomModels

/-! # K-flat extension from a point

Source: Stacks Project, Tags 0G7E and 00WJ.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace WeilConjectures.PointDerivedHom

variable (k : Type t) [Field k]
  {R : CommRingCat.{max u (t + 1)}}
  (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{max u (t + 1)})
  (α : constantRing.{t, u} k R ⟶ B)
  (L : ModuleCat.{max u (t + 1)} R ⥤ Modules.{t, u} k B)
  (hobj : ∀ M : ModuleCat.{max u (t + 1)} R,
    L.obj M = extensionObject.{t, u} k B α M)
  (hmap : ∀ {M N : ModuleCat.{max u (t + 1)} R} (f : M ⟶ N),
    L.map f = eqToHom (hobj M) ≫ extensionMorphism.{t, u} k B α f ≫
      eqToHom (hobj N).symm)
  (adj : L ⊣ sections.{t, u} k B α)
  (c : CochainComplex (ModuleCat.{max u (t + 1)} R) ℤ)

include hobj hmap

/-- Tensor extension of a flat-term K-flat module complex is K-flat on the point site.
Source: Stacks Project, Tag 0G7E, lemma-pullback-K-flat, and Tag 00WJ
(blueprint: lem-pod-point-extension-kflat).

Proof: regard modules as module sheaves on the one-object site with the trivial
covering topology. The constant-sheaf functor to the point's pro-etale site is
left adjoint to sections, since maps out of the constant presheaf are determined
by their values at the final object. It preserves finite limits: the constant
presheaf functor does so objectwise and associated sheafification is left exact.
Its algebraic inverse image on modules is the constant-module construction used
in extensionObject. The specified object and morphism equalities identify L with
this inverse image followed by scalar extension along α. Apply the ringed-topos
K-flat pullback theorem to c. Its hypotheses are exactly the assumed acyclicity
of every acyclic test tensor and flatness in each degree; module sheaves on the
one-object site have the same tensor, acyclicity and flatness as ordinary modules.
The resulting K-flat predicate is the independent-coefficient predicate here.
This includes zero modules and unbounded complexes; no boundedness or exactness
of scalar extension is asserted. -/
theorem point_extension_kflat
    (hc : ∀ F : CochainComplex (ModuleCat.{max u (t + 1)} R) ℤ,
      F.Acyclic → (moduleTotal F c).Acyclic)
    (hflat : ∀ p : ℤ, Module.Flat R (c.X p)) :
    CochainComplex.IsKFlatIndependentCoefficients (R := B)
      ((extensionComplex.{t, u} k B α L adj).obj c) := by
  sorry

end WeilConjectures.PointDerivedHom
