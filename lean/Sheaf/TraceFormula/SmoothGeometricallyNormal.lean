/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions


/-!
# Smooth schemes over fields are geometrically normal

Source: Stacks Project, `literature/stacks-project/varieties.tex`, Tag 056T,
lemma-smooth-geometrically-normal (blueprint: lem-trf-smooth-geometrically-normal).

The theorem states all three conclusions in the source.  For every finite purely
inseparable field extension, the scheme-theoretic base change is regular.  For
every field extension, each stalk of the base change is an integrally closed
domain and the base change is reduced.  The proof follows the source: smoothness
survives arbitrary field base change; finite type affine charts over a field are
Noetherian; the smooth regularity criterion gives regular local rings; regular
schemes are normal; and a domain has no nonzero nilpotents.  Empty schemes are
covered by the universal stalk quantifiers.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A scheme smooth over a field is geometrically regular, geometrically normal,
and geometrically reduced.

Source: Stacks Project, `literature/stacks-project/varieties.tex`, Tag 056T,
lemma-smooth-geometrically-normal (blueprint: lem-trf-smooth-geometrically-normal).

Proof following the node:
1. For any field extension `K/k`, smoothness survives base change by clause (2) of
   `lem-pc-proper-base-change` (Stacks, Tag 01VB).
2. By `def-sbc-smooth-morphisms`, the base-changed morphism is locally of finite
   presentation (`def-sbc-locally-finite-presentation`), hence locally of finite type.
   Affine neighbourhoods over the one-point scheme `Spec K` are finite type by
   `def-weil-finite-type-morphism`.
3. The field `K` is Noetherian (`def-weil-pbc-noetherian-ring`). Apply
   `lem-weil-pbc-finite-type-over-noetherian` to each affine neighbourhood, giving
   a Noetherian affine open cover. Thus `pqf-def-locnoeth` gives local Noetherianity;
   a finite cover of the whole scheme is not needed.
4. Apply `lem-weil-pbc-geometric-regularity-smooth-field-criterion` over `K` with
   the identity field extension. By `def-pc-base-change`, this identity base change
   is isomorphic to the given scheme, so all its stalks are regular local rings.
   Together with Step 3 this gives `IsRegularScheme`, exactly the locally Noetherian
   and stalkwise regular condition of `def-weil-regular-scheme` (Stacks, Tag 02IT).
   Specialize to finite purely inseparable `K'/k` for the first conclusion.
5. By the same Tag 02IT, the regular scheme of Step 4 has regular Noetherian affine
   neighbourhoods. Clause (1) of `rem-pc-regular-normal` therefore makes every stalk
   a domain integrally closed in its fraction field (`def-weil-pbc-normal-ring`).
6. Domains have no nonzero nilpotents. By `def-pc-reduced-scheme`, reduced stalks
   imply that the base-changed scheme is reduced. Steps 5 and 6 hold for every
   field extension, also when the base change is empty.
-/
theorem smooth_geometrically_normal
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (.of k)) [Smooth f] :
    (∀ (K' : Type u) [Field K'] [Algebra k K'] [Module.Finite k K']
      [IsPurelyInseparable k K'],
      IsRegularScheme
        (Limits.pullback (C := Scheme.{u}) f
          (Spec.map (CommRingCat.ofHom (algebraMap k K'))))) ∧
      (∀ (K : Type u) [Field K] [Algebra k K],
        (∀ x : Limits.pullback (C := Scheme.{u}) f
            (Spec.map (CommRingCat.ofHom (algebraMap k K))),
          IsDomain
              ((Limits.pullback (C := Scheme.{u}) f
                (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk x) ∧
            IsIntegrallyClosed
              ((Limits.pullback (C := Scheme.{u}) f
                (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk x)) ∧
        IsReduced
          (Limits.pullback (C := Scheme.{u}) f
            (Spec.map (CommRingCat.ofHom (algebraMap k K))))) := by
  -- Apply the existing smooth-regular and regular-normal theorems after base change.
  have hregular (K : Type u) [Field K] [Algebra k K] :
      IsRegularScheme (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
    let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
    exact ⟨LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f g),
      IsRegular.of_smooth (pullback.snd f g)⟩
  refine ⟨fun K' _ _ _ _ ↦ hregular K', ?_⟩
  intro K _ _
  have : IsRegular (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    (hregular K).2
  exact ⟨fun x ↦ ⟨inferInstance, IsRegular.isIntegrallyClosed_stalk x⟩,
    isReduced_of_isReduced_stalk _⟩

end AlgebraicGeometry

