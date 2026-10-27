/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Yoneda

/-! # Veronese line quotients on scheme tests

Source: Stacks Project, Constructions, Tags 01NW, 01NY and equation-proj
(blueprint: def-sfb-scheme-veronese-quotient-data).

The algebra uses the existing quasi-coherent affine-basis presentation. A homogeneous
map is recorded by its adjoint on affine-base sections. Local finite linear combinations
express surjectivity of the tensor-pullback degree-one map. No finite-type or degree-zero
identification is required. Restriction is specified by its graph, so the compatible-family
construction contains no choice of a map whose well-definedness is still to be proved.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory Opposite TopologicalSpace MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
noncomputable section

namespace AlgebraicGeometry.Scheme.VeroneseQuotient

/-- An open test with its inherited base morphism.
Source: Stacks, equation-proj (blueprint: def-sfb-scheme-veronese-quotient-data). -/
def openTest {S : Scheme.{u}} (T : Over S) (V : T.left.Opens) : Over S :=
  Over.mk (V.ι ≫ T.hom)

/-- A positive Veronese line quotient, in the adjoint affine-basis presentation.
The last field says exactly that the images of degree-one sections generate locally,
and hence that the map from tensor pullback is a sheaf surjection.
Source: Stacks, 01NV and 01NW (blueprint: def-sfb-scheme-veronese-quotient-data). -/
structure Datum {S : Scheme.{u}} (Z : Over S) (A : Z.left.GradedAlgebraData)
    (T : Over S) where
  d : ℕ
  positive : 0 < d
  f : T ⟶ Z
  L : T.left.Modules
  invertible : L.IsInvertible
  ψ : ∀ (V : Z.left.affineOpens) (n : ℕ),
    A.grading V (d * n) →+ Γ(L.tensorPow n, f.left ⁻¹ᵁ V.1)
  scalar : ∀ (V : Z.left.affineOpens) (n : ℕ) (r : Γ(Z.left, V.1))
    (b : A.grading V (d * n)),
    ψ V n (r • b) = f.left.app V.1 r • ψ V n b
  naturality : ∀ (V W : Z.left.affineOpens) (h : W ≤ V) (n : ℕ)
    (b : A.grading V (d * n)),
    (L.tensorPow n).presheaf.map (homOfLE (f.left.preimage_mono h)).op (ψ V n b) =
      ψ W n ⟨A.res h b, (A.res h).map_mem b.property⟩
  unit : ∀ V : Z.left.affineOpens,
    HEq (ψ V 0 ⟨1, SetLike.one_mem_graded (A.grading V)⟩)
      (unitSectionsEquiv (f.left ⁻¹ᵁ V.1) 1)
  mul : ∀ (V : Z.left.affineOpens) (m n : ℕ)
    (b : A.grading V (d * m)) (c : A.grading V (d * n)),
    HEq (ψ V (m + n)
      ⟨b.val * c.val, by
        simpa only [Nat.mul_add] using SetLike.GradedMul.mul_mem b.property c.property⟩)
      ((L.tensorPowAddIso m n).inv.app (f.left ⁻¹ᵁ V.1)
        (tmulSection (ψ V m b) (ψ V n c)))
  surjective : ∀ (V : Z.left.affineOpens) (W : T.left.Opens)
    (hW : W ≤ f.left ⁻¹ᵁ V.1) (s : Γ(L.tensorPow 1, W))
    (x : T.left) (_hx : x ∈ W),
    ∃ (W' : T.left.Opens) (h : W' ≤ W) (_hx' : x ∈ W')
      (r : ℕ) (b : Fin r → A.grading V (d * 1)) (c : Fin r → Γ(T.left, W')),
      (L.tensorPow 1).presheaf.map (homOfLE h).op s =
        ∑ i : Fin r, c i • (L.tensorPow 1).presheaf.map
          (homOfLE (h.trans hW)).op (ψ V 1 (b i))

/-- Common-positive-multiple equivalence, including the degree-zero component.
`HEq` only transports the equal degrees and equal inverse-image opens.
Source: Stacks, 01NW(3) (blueprint: def-sfb-scheme-veronese-quotient-data). -/
def Equivalent {S : Scheme.{u}} {Z : Over S} {A : Z.left.GradedAlgebraData}
    {T : Over S} (a b : Datum Z A T) : Prop :=
  a.f = b.f ∧ ∃ (k l : ℕ), 0 < k ∧ 0 < l ∧ a.d * k = b.d * l ∧
    ∃ β : a.L.tensorPow k ≅ b.L.tensorPow l,
      ∀ (V : Z.left.affineOpens) (n : ℕ)
        (s : A.grading V (a.d * (k * n))),
        ∃ t : A.grading V (b.d * (l * n)), s.val = t.val ∧
          HEq (((a.L.tensorPowMulIso k n).hom ≫
            (boundaryTensorPowIso β n).hom ≫ (b.L.tensorPowMulIso l n).inv).app
              (a.f.left ⁻¹ᵁ V.1) (a.ψ V (k * n) s)) (b.ψ V (l * n) t)

/-- The quotient by common-power identifications. Equivalence of the displayed relation
is a clause of the representing theorem, not an assumption of this construction.
Source: Stacks, 01NW (blueprint: def-sfb-scheme-veronese-quotient-data). -/
def Classes {S : Scheme.{u}} (Z : Over S) (A : Z.left.GradedAlgebraData)
    (T : Over S) : Type (u + 1) :=
  Quot (Equivalent (Z := Z) (A := A) (T := T))

/-- The class of a literal datum.
Source: Stacks, 01NW (blueprint: def-sfb-scheme-veronese-quotient-data). -/
def classOf {S : Scheme.{u}} {Z : Over S} {A : Z.left.GradedAlgebraData}
    {T : Over S} (a : Datum Z A T) : Classes Z A T :=
  Quot.mk _ a

/-- A datum is the tensor pullback of another, up to its strict line isomorphism.
The section equation fixes all homogeneous components, including the unit component.
Source: Stacks, equation-proj (blueprint: def-sfb-scheme-veronese-quotient-data). -/
def PullsDatum {S : Scheme.{u}} {Z : Over S} {A : Z.left.GradedAlgebraData}
    {T T' : Over S} (u : T' ⟶ T) (a : Datum Z A T) (b : Datum Z A T') : Prop :=
  a.d = b.d ∧ u ≫ a.f = b.f ∧
    ∃ β : (tensorPullback u.left).obj a.L ≅ b.L,
      ∀ (V : Z.left.affineOpens) (n : ℕ) (s : A.grading V (a.d * n)),
        ∃ t : A.grading V (b.d * n), s.val = t.val ∧
          HEq (((boundaryPullbackPowIso u.left a.L n).hom ≫
            (boundaryTensorPowIso β n).hom).app
              (u.left ⁻¹ᵁ (a.f.left ⁻¹ᵁ V.1))
              (tensorPullbackSection u.left (a.L.tensorPow n)
                (a.f.left ⁻¹ᵁ V.1) (a.ψ V n s))) (b.ψ V n t)

/-- The graph of pullback on classes. Its totality and uniqueness are theorem clauses.
Source: Stacks, equation-proj (blueprint: def-sfb-scheme-veronese-quotient-data). -/
def Pulls {S : Scheme.{u}} {Z : Over S} {A : Z.left.GradedAlgebraData}
    {T T' : Over S} (u : T' ⟶ T) (a : Classes Z A T) (b : Classes Z A T') : Prop :=
  ∃ (a₀ : Datum Z A T) (b₀ : Datum Z A T'),
    classOf a₀ = a ∧ classOf b₀ = b ∧ PullsDatum u a₀ b₀

/-- The actual quasi-compact opens; no intersection-compactness condition is imposed.
Source: Stacks, equation-proj (blueprint: def-sfb-scheme-veronese-quotient-data). -/
def CompactOpens {S : Scheme.{u}} (T : Over S) :=
  {V : T.left.Opens // IsCompact (V : Set T.left)}

/-- A compatible family over quasi-compact opens, the concrete inverse-limit set.
Compatibility uses the graph of the specified restriction on classes.
Source: Stacks, equation-proj (blueprint: def-sfb-scheme-veronese-quotient-data). -/
def Sections {S : Scheme.{u}} (Z : Over S) (A : Z.left.GradedAlgebraData)
    (T : Over S) : Type (u + 1) :=
  {q : ∀ V : CompactOpens T, Classes Z A (openTest T V.val) //
    ∀ (V W : CompactOpens T) (i : openTest T W.val ⟶ openTest T V.val),
      i.left ≫ V.val.ι = W.val.ι → Pulls i (q V) (q W)}

/-- Evaluation on the whole test, when it is quasi-compact. Keeping the canonical top
open as an open test avoids choosing an identification of it with the original scheme.
Source: Stacks, equation-proj (blueprint: def-sfb-scheme-veronese-quotient-data). -/
def topComponent {S : Scheme.{u}} {Z : Over S} {A : Z.left.GradedAlgebraData}
    {T : Over S} (hT : IsCompact (Set.univ : Set T.left)) (q : Sections Z A T) :
    Classes Z A (openTest T ⊤) :=
  q.val ⟨⊤, hT⟩

/-- A compatible family remembers the structural morphism degreewise.
Source: Stacks, 01NY (blueprint: def-sfb-scheme-veronese-quotient-data). -/
def Remembers {S : Scheme.{u}} {Z : Over S} {A : Z.left.GradedAlgebraData}
    {T : Over S} (q : Sections Z A T) (f : T ⟶ Z) : Prop :=
  ∀ V : CompactOpens T, ∃ a : Datum Z A (openTest T V.val),
    classOf a = q.val V ∧ a.f.left = V.val.ι ≫ f.left

/-- Precomposition of a quotient by a base-linear graded algebra isomorphism.
Source: Stacks, 01NZ (blueprint: def-sfb-scheme-veronese-quotient-data). -/
def IsoActsDatum {S : Scheme.{u}} {Z : Over S} {A B : Z.left.GradedAlgebraData}
    {T : Over S} (e : A ≅ B) (b : Datum Z B T) (a : Datum Z A T) : Prop :=
  b.d = a.d ∧ b.f = a.f ∧ ∃ β : b.L ≅ a.L,
    ∀ (V : Z.left.affineOpens) (n : ℕ) (s : A.grading V (a.d * n)),
      ∃ t : B.grading V (b.d * n), (e.hom.app V s.val) = t.val ∧
        HEq ((boundaryTensorPowIso β n).hom.app (b.f.left ⁻¹ᵁ V.1)
          (b.ψ V n t)) (a.ψ V n s)

/-- The algebra-isomorphism operation on classes.
Source: Stacks, 01NZ (blueprint: def-sfb-scheme-veronese-quotient-data). -/
def IsoActs {S : Scheme.{u}} {Z : Over S} {A B : Z.left.GradedAlgebraData}
    {T : Over S} (e : A ≅ B) (b : Classes Z B T) (a : Classes Z A T) : Prop :=
  ∃ (b₀ : Datum Z B T) (a₀ : Datum Z A T),
    classOf b₀ = b ∧ classOf a₀ = a ∧ IsoActsDatum e b₀ a₀

/-- The canonical scheme over the original base, using the existing glued Proj.
Source: Stacks, 01NZ (blueprint: def-sfb-scheme-veronese-quotient-data). -/
def projTest {S : Scheme.{u}} (Z : Over S) (A : Z.left.GradedAlgebraData) : Over S :=
  Over.mk (A.relProjHom ≫ Z.hom)

/-- Its structural morphism to the base of the graded algebra.
Source: Stacks, 01NZ (blueprint: def-sfb-scheme-veronese-quotient-data). -/
def projBase {S : Scheme.{u}} (Z : Over S) (A : Z.left.GradedAlgebraData) :
    projTest Z A ⟶ Z :=
  Over.homMk A.relProjHom

/-- Twisting-sheaf normalization on an affine-base chart. Each homogeneous component
identifies with the pullback of the actual `Proj.twist`, carrying `b` to `b/1`.
Because degree-one images generate the line, these identifications are forced by the
first one and multiplication, and are precisely the canonical tensor-power identifications.
Source: Stacks, 01NZ, second proof (blueprint: def-sfb-scheme-veronese-quotient-data). -/
def Normalized {S : Scheme.{u}} {Z : Over S} {A : Z.left.GradedAlgebraData}
    {T : Over S} (a : Datum Z A T) (V : Z.left.affineOpens)
    (g : T.left ⟶ Proj (A.grading V)) : Prop :=
  (∀ x : T.left, a.f.left.base x ∈ V.1) ∧
    ∃ β : ∀ n : ℕ, a.L.tensorPow n ≅
      (tensorPullback g).obj (Proj.twist (A.grading V) (0 + ((a.d * n : ℕ) : ℤ))),
      ∀ (n : ℕ) (b : A.grading V (a.d * n)),
        HEq ((β n).hom.app (a.f.left ⁻¹ᵁ V.1) (a.ψ V n b))
          (tensorPullbackSection g (Proj.twist (A.grading V) (0 + ((a.d * n : ℕ) : ℤ))) ⊤
            ((Proj.unitToTwist b.property).app ⊤ (unitSectionsEquiv ⊤ 1)))

/-- The ordinary contravariant Proj map, regarded as a map over the original base.
Source: Stacks, 01NZ (blueprint: def-sfb-scheme-veronese-quotient-data). -/
def projIsoHom {S : Scheme.{u}} {Z : Over S} {A B : Z.left.GradedAlgebraData}
    (e : A ≅ B) : projTest Z B ⟶ projTest Z A :=
  Over.homMk (GradedAlgebraData.relProjIsoOfIso e).hom (by
    simp only [projTest, Over.mk_hom, ← Category.assoc,
      GradedAlgebraData.relProjIsoOfIso_hom_relProjHom])

/-- An actual set-valued functor with its prescribed compatible-family objects and
normalized representing natural bijection. All laws are properties, not chosen data.
Source: Stacks, 01NW, equation-proj, 01NY and 01NZ
(blueprint: def-sfb-scheme-veronese-quotient-data). -/
structure Representation {S : Scheme.{u}} (Z : Over S) (A : Z.left.GradedAlgebraData) where
  functor : (Over S)ᵒᵖ ⥤ Type (u + 1)
  sections : ∀ T : Over S, functor.obj (op T) ≃ Sections Z A T
  represent : uliftYoneda.{u + 1}.obj (projTest Z A) ≅ functor
  equivalence : ∀ T : Over S, Equivalence (Equivalent (Z := Z) (A := A) (T := T))
  pullback_unique : ∀ (T T' : Over S) (u : T' ⟶ T) (q : Classes Z A T),
    ∃! q' : Classes Z A T', Pulls u q q'
  quasiCompact : ∀ (T : Over S) (hT : IsCompact (Set.univ : Set T.left)),
    Function.Bijective (topComponent (Z := Z) (A := A) hT)
  pullback : ∀ (T T' : Over S) (u : T' ⟶ T) (q : functor.obj (op T))
    (V : CompactOpens T) (W : CompactOpens T')
    (v : openTest T' W.val ⟶ openTest T V.val),
    v.left ≫ V.val.ι = W.val.ι ≫ u.left →
      Pulls v ((sections T q).val V) ((sections T' (functor.map u.op q)).val W)
  base : ∀ (T : Over S) (g : T ⟶ projTest Z A),
    Remembers (sections T (represent.hom.app (op T) ⟨g⟩)) (g ≫ projBase Z A)
  normalized : ∀ (T : Over S) (g : T ⟶ projTest Z A) (W : CompactOpens T)
    (a : Datum Z A (openTest T W.val)),
    classOf a = (sections T (represent.hom.app (op T) ⟨g⟩)).val W →
      ∀ (V : Z.left.affineOpens) (h : W.val.toScheme ⟶ Proj (A.grading V)),
        h ≫ A.relProjι V = W.val.ι ≫ g.left → Normalized a V h

end AlgebraicGeometry.Scheme.VeroneseQuotient
