/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Finite support diagrams for the open counit

Source: Stacks Project, Tags 00WK and 09AE; finite representatives and the
smaller-open comparison in Steps 9--11 of
`lem-exc-proetale-proper-open-sheaf-comparison`.
(blueprint: lem-exc-proetale-open-counit-finite-support-diagram)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (A : Type u) [CommRing A] [Finite A]

/-- A section of the pushforward of an open extension has a finite support diagram
coming from a quasi-compact open in the affine test object. The maps `a` and `b` are
homomorphisms of section groups and intertwine the two specified open counits.
Properness is not assumed: quasi-compactness and quasi-separatedness suffice for
this finite-representative step, which makes no surjectivity assertion about either
counit.

Source: Stacks Project, Tags 00WK and 09AE; Steps 9--11 of the support argument in
`lem-exc-proetale-proper-open-sheaf-comparison`.
(blueprint: lem-exc-proetale-open-counit-finite-support-diagram).

Proof: first localize at `Q`. Weakly etale base change identifies direct-image
sections with sections over `V ×_T Q`, and open-extension base change identifies its
sheaf with the extension from the pulled-back open. This inverse image of `Q` is
quasi-compact and quasi-separated. By local surjectivity of the sheafification unit,
the section has presheaf representatives on a pro-etale cover. Refine to finitely
many affine representatives using the quasi-compact covering condition. Each nonzero
representative factors through the pulled-back open. Its image in the affine scheme
`Q` is quasi-compact and contained in that open, so finitely many principal opens
inside it cover all these images. Let `O` be their union. It is quasi-compact, is
contained in the inverse image of `W`, and may be empty if every representative is
zero. Put `M₀` equal to the restriction of the localized original module to the inverse
image of `O`. Lift each representative to its extension by zero, using zero for the
remaining representatives. The map from this smaller extension into the original
one is monic: presheaf zero extension is monic and sheafification is exact. Thus the
lifts agree on overlaps and glue to `y₀`. Push the smaller-open inclusion forward and
use the canonical localization section comparison to obtain `b`; this gives
`b y₀ = y`. Extend the corresponding restricted map by zero from `O` into the
pulled-back `W` and then use the same localization comparison to obtain `a`.
Transposing both composites under the `O`-open adjunction gives the same restriction
map, by naturality and the triangle identities. Hence they intertwine the specified
counits as displayed. All maps are module maps before forgetting to section groups.
The argument uses neither properness nor preservation of arbitrary colimits by
direct image. Empty test objects and empty supports are covered by the empty family. -/
theorem sfOpenCounit_finiteSupportDiagram {V W T : Scheme.{u}} (p : V ⟶ T)
    [QuasiCompact p] [QuasiSeparated p] (i : W ⟶ T) [IsOpenImmersion i]
    (M : proEtaleRingModules (pullback p i)
      (proEtaleConstantRing (pullback p i) A)) (Q : T.ProEt) [IsAffine Q.left] :
    let F := (sfIntrinsicExtensionByZero (pullback.fst p i) A ⋙
      proEtaleConstantModuleDirectImage p A).obj M
    let c := (sfIntrinsicExtensionByZeroAdjunction i A).counit.app F
    ∀ y : F.val.obj (op Q),
      ∃ (O : Q.left.Opens) (_ : IsCompact (O : Set Q.left))
        (_ : (O : Set Q.left) ⊆ Q.hom ⁻¹' Set.range i)
        (M₀ : proEtaleRingModules (pullback (pullback.snd p Q.hom) O.ι)
          (proEtaleConstantRing (pullback (pullback.snd p Q.hom) O.ι) A)),
        let F₀ := (sfIntrinsicExtensionByZero
          (pullback.fst (pullback.snd p Q.hom) O.ι) A ⋙
            proEtaleConstantModuleDirectImage (pullback.snd p Q.hom) A).obj M₀
        let c₀ := (sfIntrinsicExtensionByZeroAdjunction O.ι A).counit.app F₀
        ∃ (a : ((sfIntrinsicExtensionByZero O.ι A).obj
            ((sfIntrinsicOpenRestriction O.ι A).obj F₀)).val.obj (op (ProEt.mk (𝟙 Q.left))) →+
              ((sfIntrinsicExtensionByZero i A).obj
                ((sfIntrinsicOpenRestriction i A).obj F)).val.obj (op Q))
          (b : F₀.val.obj (op (ProEt.mk (𝟙 Q.left))) →+ F.val.obj (op Q))
          (y₀ : F₀.val.obj (op (ProEt.mk (𝟙 Q.left)))),
          (∀ x, c.val.app (op Q) (a x) =
            b (c₀.val.app (op (ProEt.mk (𝟙 Q.left))) x)) ∧ b y₀ = y := by
  sorry

end AlgebraicGeometry.Scheme
