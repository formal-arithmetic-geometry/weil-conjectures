module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.ModuliChartNormalization
public import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests

/-! # Smooth presentations of morphisms of algebraic stacks

Source: Stacks Project, Morphisms of Stacks, Tags 06FM and 075U; Criteria for
Representability, Tag 076V (blueprint: lem-sfb-stack-smooth-presentation-criterion).

The four chart conditions use the existing scheme smoothness, algebraic-space chart
extension, representable scheme tests, field-extension surjectivity and 2-fibre products.
Only the source vertical map is required to be surjective in the existential tests.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry

namespace CategoryTheory

/-- An algebraic-space diagram over a stack morphism with representable smooth vertical maps.
Its specified based natural isomorphism is the 2-commutativity of the square.
Source: Stacks Project, Tag 06FM
(blueprint: lem-sfb-stack-smooth-presentation-criterion). -/
structure SmoothModuliPresentation {S : Scheme.{u}}
    {X : BasedCategory.{v₁, w₁} (Over S)} {Y : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor X Y) where
  U : AlgebraicSpace S
  V : AlgebraicSpace S
  a : BasedFunctor (discreteModuli U.obj.obj) X
  b : BasedFunctor (discreteModuli V.obj.obj) Y
  q : U ⟶ V
  comm : a.comp f ≅ (discreteModuliMap q.hom.hom).comp b
  source_smooth : ModuliSpaceTest (@Smooth) a
  target_smooth : ModuliSpaceTest (@Smooth) b

/-- The same diagram with both charts schemes; no surjectivity is built into this data.
Source: Stacks Project, Tag 06FM, refined by étale scheme atlases
(blueprint: lem-sfb-stack-smooth-presentation-criterion). -/
structure SmoothSchemeModuliPresentation {S : Scheme.{u}}
    {X : BasedCategory.{v₁, w₁} (Over S)} {Y : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor X Y) where
  U : Over S
  V : Over S
  a : BasedFunctor (discreteModuli (yoneda.obj U)) X
  b : BasedFunctor (discreteModuli (yoneda.obj V)) Y
  q : U ⟶ V
  comm : a.comp f ≅ (discreteModuliMap (yoneda.map q)).comp b
  source_smooth : ModuliSpaceTest (@Smooth) a
  target_smooth : ModuliSpaceTest (@Smooth) b

/-- Condition A, the universal smooth-chart test for arbitrary algebraic-stack morphisms.
The additional smoothness test is on the canonical map to the 2-fibre product.
The name `IsSmoothModuliMap` belongs to the definition node def-sfb-smooth-moduli-map.
Source: Stacks Project, Tags 06FM and 075U
(blueprint: lem-sfb-stack-smooth-presentation-criterion). -/
def IsSmoothOnModuliPresentations {S : Scheme.{u}}
    {X : BasedCategory.{v₁, w₁} (Over S)} {Y : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor X Y) : Prop :=
  ∀ D : SmoothModuliPresentation f,
    ModuliSpaceTest (@Smooth)
      (moduliTwoFiberLift D.a (discreteModuliMap D.q.hom.hom) D.comm) →
    AlgebraicSpace.MapIsLocally (@Smooth) D.q

/-- Condition B: one diagram with surjective source vertical map and smooth horizontal map.
There is no condition on its induced map to the 2-fibre product or on target surjectivity.
Source: Stacks Project, Tag 06FM
(blueprint: lem-sfb-stack-smooth-presentation-criterion). -/
def HasSmoothModuliPresentation {S : Scheme.{u}}
    {X : BasedCategory.{v₁, w₁} (Over S)} {Y : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor X Y) : Prop :=
  ∃ D : SmoothModuliPresentation f,
    IsSurjectiveModuliMap D.a ∧ AlgebraicSpace.MapIsLocally (@Smooth) D.q

/-- Condition A restricted to schemes, using the actual induced comparison of the square.
Source: Stacks Project, Tag 06FM, refined by étale scheme atlases
(blueprint: lem-sfb-stack-smooth-presentation-criterion). -/
def IsSmoothOnSchemeModuliPresentations {S : Scheme.{u}}
    {X : BasedCategory.{v₁, w₁} (Over S)} {Y : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor X Y) : Prop :=
  ∀ D : SmoothSchemeModuliPresentation f,
    ModuliSpaceTest (@Smooth)
      (moduliTwoFiberLift D.a (discreteModuliMap (yoneda.map D.q)) D.comm) →
    Smooth D.q.left

/-- Condition B restricted to scheme charts, with surjectivity only on the source.
Source: Stacks Project, Tag 06FM, refined by étale scheme atlases
(blueprint: lem-sfb-stack-smooth-presentation-criterion). -/
def HasSmoothSchemeModuliPresentation {S : Scheme.{u}}
    {X : BasedCategory.{v₁, w₁} (Over S)} {Y : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor X Y) : Prop :=
  ∃ D : SmoothSchemeModuliPresentation f, IsSurjectiveModuliMap D.a ∧ Smooth D.q.left

/-- All four smooth presentation conditions for a general algebraic-stack morphism agree.
Source: Stacks Project, Tags 06FM and 075U
(blueprint: lem-sfb-stack-smooth-presentation-criterion).

Proof:
1. Identify ordinary smooth space maps with representable smooth maps by scheme tests:
   refine with étale atlases, apply lem-sfb-space-etale-presentation-property-criterion
   and lem-sfb-scheme-etale-source-target-properties in both directions. Use
   lem-trf-space-representable-etale-scheme-tests for chart refinement. Identify
   field-extension surjectivity with the atlas chart test by lifting residue-field
   points, using def-sfb-stable-pointed-moduli-groupoids and def-sfb-algebraic-moduli-stack.
2. Assuming the universal scheme condition, choose a smooth surjective scheme atlas
   V → Y and a smooth surjective scheme atlas U → X ×_Y V. The fibre product is
   algebraic by lem-sfb-algebraic-stack-fibre-products. The representable calculus
   lem-sfb-fibred-groupoid-representable-smooth-calculus makes U → X smooth surjective.
   The induced map is the second atlas, so the universal test makes U → V smooth.
3. Given a diagram satisfying B and any diagram U' → V' tested by A, form the spaces
   E = V ×_Y V', D = U ×_Y V', P = U ×_X U', using
   lem-sfb-representable-pullback-over-space. The triple description of
   def-sfb-stable-pointed-moduli-groupoids identifies P → D as a base change of
   U' → X ×_Y V'. The map D → E is the base change of U → V, and E → V' is a base
   change of V → Y. All three are smooth by the representable calculus and
   lem-sfb-space-smooth-surjective-fppf-locality. Hence P → V' is smooth.
4. P → U' is smooth surjective, being the base change of U → X. At every point of
   U', lift a point to P and apply lem-sfb-space-smooth-source-point-locality to
   descend smoothness of U' → V'. Scheme source locality glues these neighbourhoods.
   This proves B implies A, without surjectivity of either target chart.
5. Restriction gives A implies A_scheme. Step 2 gives A_scheme implies B_scheme,
   and schemeSpace of def-trf-scheme-algebraic-space gives B_scheme implies B.
   Together with steps 3--4, this proves all four conditions equivalent. -/
theorem stack_smooth_presentation_criterion {S : Scheme.{u}}
    {X : BasedCategory.{v₁, w₁} (Over S)} {Y : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor X Y) (hX : IsAlgebraicModuliStack X)
    (hY : IsAlgebraicModuliStack Y) :
    (IsSmoothOnModuliPresentations f ↔ HasSmoothModuliPresentation f) ∧
      (IsSmoothOnModuliPresentations f ↔ IsSmoothOnSchemeModuliPresentations f) ∧
      (IsSmoothOnModuliPresentations f ↔ HasSmoothSchemeModuliPresentation f) := by
  sorry

/-- For maps of algebraic spaces, the chart definition agrees with ordinary smoothness.
Source: Stacks Project, Tag 06FM, algebraic-space comparison paragraph
(blueprint: lem-sfb-stack-smooth-presentation-criterion).

Proof (step 6 of the node): first use the scheme tests, the étale presentation
criterion and scheme étale locality to identify ordinary and representable smoothness,
as in step 1 of stack_smooth_presentation_criterion. If f is smooth, the projection
X ×_Y V → V is representable smooth by base change. Its composite with the smooth
induced U → X ×_Y V is smooth, so A holds, by
lem-sfb-fibred-groupoid-representable-smooth-calculus. Conversely take U = X, V = Y,
with both vertical maps identities. They and the induced X → X ×_Y Y are smooth
(the last is an isomorphism). The test A then asserts ordinary smoothness of f.
Identities of schemes are smooth directly from def-sbc-smooth-morphisms. -/
theorem isSmoothOnModuliPresentations_iff_space_smooth {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    IsSmoothOnModuliPresentations (discreteModuliMap f.hom.hom) ↔
      AlgebraicSpace.MapIsLocally (@Smooth) f := by
  sorry

/-- For a representable map, smoothness agrees with smoothness of every scheme base change.
The space test retains the actual projection, through HasSpaceBaseChange.
Source: Stacks Project, Tags 06FM and 075U, representable comparison paragraph
(blueprint: lem-sfb-stack-smooth-presentation-criterion).

Proof:
1. Suppose B holds and let T → Y be a scheme test. Set W = X ×_Y T,
   U_T = U ×_Y T and V_T = V ×_Y T. Representability gives spaces, using
   lem-sfb-representable-pullback-over-space. The representable calculus makes
   U_T → W smooth surjective and V_T → T smooth.
2. The triple description of def-sfb-stable-pointed-moduli-groupoids identifies
   U_T → V_T with the base change of U → V: insert or forget v = q(u) in
   U ×_V (V ×_Y T). Thus U_T → V_T → T is smooth. By
   lem-sfb-space-smooth-source-point-locality along U_T → W and scheme source
   locality, W → T is smooth. Step 1 of stack_smooth_presentation_criterion
   identifies this with the stated scheme-test predicate. No cover of T is needed.
3. Conversely assume every scheme base change is smooth. This is representable
   smoothness by definition. In any diagram tested by A, compose U → X ×_Y V
   with the smooth projection to V. The representable calculus and the space
   comparison of step 1 give ordinary smoothness of U → V, so A holds. -/
theorem isSmoothOnModuliPresentations_iff_representable_smooth {S : Scheme.{u}}
    {X : BasedCategory.{v₁, w₁} (Over S)} {Y : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor X Y) (hX : IsAlgebraicModuliStack X)
    (hY : IsAlgebraicModuliStack Y) (hf : IsRepresentableByAlgebraicSpaces f) :
    IsSmoothOnModuliPresentations f ↔ ModuliSpaceTest (@Smooth) f := by
  sorry

end CategoryTheory
