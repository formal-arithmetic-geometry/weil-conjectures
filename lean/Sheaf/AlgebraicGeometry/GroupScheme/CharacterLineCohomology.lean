module

public import Sheaf.AlgebraicGeometry.GroupScheme.AssociatedCharacterLineBundle
public import Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData
public import Sheaf.AlgebraicGeometry.GroupSchemeLinearization
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap

/-! # Homogeneous character-line cohomology with its specified rational action

Source: Milne, Algebraic Groups (2017), Section 18c and Definition 22.21;
Stacks Project, Tags 01F7, 01FB and 02KH.
(blueprint: def-sfb-character-line-cohomology)

The cohomology is the existing right-derived module global-sections functor,
with scalars restricted to F. The universal coaction identity below uses the
canonical cohomology maps on G times Q. Thus it specifies the algebraic action,
including every scalar extension, without substituting an arbitrary representation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj TensorProduct
namespace AlgebraicGeometry.CharacterLineCohomology
open AssociatedCharacterLineBundle GroupSchemeLinearization RationalHighestWeight

/-- Restrict the scalars of the existing derived global-sections cohomology to F.
Source: Stacks Project, Tags 01EO and 01F7.
(blueprint: def-sfb-character-line-cohomology) -/
def cohomology {F : Type u} [Field F] (Q : Over (Spec (.of F)))
    (L : Q.left.Modules) (i : ℕ) : ModuleCat F :=
  (ModuleCat.restrictScalars
    (((Scheme.ΓSpecIso (.of F)).inv ≫ Q.hom.appTop).hom)).obj
      ((RingedSpace.moduleCohomology Q.left.toRingedSpace i).obj L)

/-- The natural linearization fixes the coordinate z in the atlas [g,z], on all
scheme-valued points. HEq only transports the equality s pi(g) = pi(sg).
Source: Milne, Section 18c, and Definition 22.21.
(blueprint: def-sfb-character-line-cohomology) -/
def IsNaturalLinearization {F : Type u} [Field F]
    {G B : Grp (Over (Spec (.of F)))} {iB : B ⟶ G}
    {Q : Over (Spec (.of F))} {π : G.X ⟶ Q}
    {χ : B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)}
    (P : Presentation G B iB Q π χ) (l : Linearization P.baseAction P.L) : Prop :=
  ∀ (Z : Over (Spec (.of F))) (s g : Z ⟶ G.X),
    HEq ((trivializationAt π P.L P.trivialization g).symm ≪≫ l.lift Z s (g ≫ π))
      (trivializationAt π P.L P.trivialization (s * g)).symm

/-- The universal action map on cohomology: pull back along (g,y) ↦ g inverse y,
then use the inverse linearization to obtain coefficients in p₂*L.
Source: Stacks Project, Tags 01F7 and 01FB; Milne, Definition 22.21.
(blueprint: def-sfb-character-line-cohomology) -/
def universalAction {F : Type u} [Field F]
    {G : Grp (Over (Spec (.of F)))} {Q : Over (Spec (.of F))}
    {L : Q.left.Modules} {A : ModObj G.X Q} (l : Linearization A L) (i : ℕ) :=
  Scheme.Modules.moduleCohomologyFMap
    (act A (G.X ⊗ Q) (fst G.X Q)⁻¹ (snd G.X Q)).left
    ((Scheme.Modules.pullbackPushforwardAdjunction
      (act A (G.X ⊗ Q) (fst G.X Q)⁻¹ (snd G.X Q)).left).homEquiv _ _
        (l.lift (G.X ⊗ Q) (fst G.X Q)⁻¹ (snd G.X Q)).inv) i

/-- Pullback along p₂, before extension of the field scalars.
Source: Stacks Project, Tags 01F7 and 02KH.
(blueprint: def-sfb-character-line-cohomology) -/
def universalPullback {F : Type u} [Field F]
    (G : Grp (Over (Spec (.of F)))) (Q : Over (Spec (.of F)))
    (L : Q.left.Modules) (i : ℕ) :=
  Scheme.Modules.moduleCohomologyFMap (snd G.X Q).left
    ((Scheme.Modules.pullbackPushforwardAdjunction (snd G.X Q).left).unit.app L) i

/-- A rational coaction is the natural cohomology action when its universal
matrix-coefficient identity is the canonical flat-base-change identity.
The implication is tested on every finite tensor expression for c(z); this is
exactly beta(c(z)) = action(z), where beta(v tensor a) = p₁*a times p₂*v.
No arbitrary base-change isomorphism or action map is supplied.
Source: Stacks Project, Tags 01FB and 02KH; Milne, Section 4a.
(blueprint: def-sfb-character-line-cohomology) -/
def IsNaturalCoaction {F : Type u} [Field F]
    {G : Grp (Over (Spec (.of F)))} [IsAffine G.X.left]
    {Q : Over (Spec (.of F))} {L : Q.left.Modules}
    {A : ModObj G.X Q} (l : Linearization A L) (i : ℕ)
    (c : cohomology Q L i →ₗ[F] cohomology Q L i ⊗[F] coordinateAlgebra G) : Prop :=
  HopfAction.Coassociative F (coordinateAlgebra G) (cohomology Q L i) c ∧
  HopfAction.Counital F (coordinateAlgebra G) (cohomology Q L i) c ∧
  ∀ (z : cohomology Q L i) (n : ℕ) (v : Fin n → cohomology Q L i)
    (a : Fin n → coordinateAlgebra G),
    c z = ∑ j, v j ⊗ₜ[F] a j →
      universalAction l i z =
        ∑ j, @SMul.smul Γ((G.X ⊗ Q).left, ⊤)
          ((RingedSpace.moduleCohomology (G.X ⊗ Q).left.toRingedSpace i).obj
            ((Scheme.Modules.pullback (snd G.X Q).left).obj L)) _
          ((fst G.X Q).left.appTop (a j)) (universalPullback G Q L i (v j))

/-- A presentation of the actual homogeneous character-line cohomology and its
natural rational left action. The bundle and linearization are normalized on
all test schemes, and coactions are normalized by universal flat base change.
This packages the objects in the source; it does not assert their existence.
Source: Milne, Section 18c and Definition 22.21; Stacks Project, Tag 02KH.
(blueprint: def-sfb-character-line-cohomology) -/
structure Data {F : Type u} [Field F]
    (G B : Grp (Over (Spec (.of F)))) [IsAffine G.X.left] (iB : B ⟶ G)
    (Q : Over (Spec (.of F))) (π : G.X ⟶ Q)
    (χ : B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) where
  /-- The associated character-line bundle, with its specified trivialization. -/
  bundle : Presentation G B iB Q π χ
  /-- The algebraic linearization of its section sheaf. -/
  linearization : Linearization bundle.baseAction bundle.L
  /-- The linearization is the natural action [g,z] ↦ [sg,z]. -/
  natural_linearization : IsNaturalLinearization bundle linearization
  /-- The coaction on right-derived global sections in every nonnegative degree. -/
  coaction : ∀ i : ℕ, cohomology Q bundle.L i →ₗ[F]
    cohomology Q bundle.L i ⊗[F] coordinateAlgebra G
  /-- The coactions are the specified cohomological action. -/
  natural_coaction : ∀ i : ℕ, IsNaturalCoaction linearization i (coaction i)

end AlgebraicGeometry.CharacterLineCohomology
