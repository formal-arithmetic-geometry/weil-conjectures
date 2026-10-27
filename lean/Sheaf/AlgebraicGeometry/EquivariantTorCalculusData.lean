module

public import Sheaf.AlgebraicGeometry.SchemeTor
public import Sheaf.AlgebraicGeometry.EquivariantCoherentGZero
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Homology.HomologySequence
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Equivariant coherent Tor calculus

Source: Stacks 08BP, 00LY, 00LS, 00M7, 00M8, 01BY and 03LF, with the
node's eleven-step action-groupoid descent argument.
(blueprint: def-sfb-equivariant-tor-calculus-data)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.SchemeTor

open CategoryTheory.CartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable (F : Type u) [Field F]

/-- An indexing type for finite-type F-schemes; its predicate is exactly the recorded
finite-type condition, with no separatedness assumption.
Source: Stacks 01T0 (blueprint: def-sfb-equivariant-tor-calculus-data). -/
abbrev Space := {X : Over (Spec (.of F)) // LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom}

/-- Coherence on the existing module category, packaged with its proof.
Source: Stacks 01BV (blueprint: def-sfb-equivariant-tor-calculus-data). -/
abbrev Coh (X : Scheme.{u}) :=
  {M : X.Modules // RingedSpace.IsCoherent X.toRingedSpace M}

/-- The actual section pullback, followed by restriction to a specified subopen.
Source: Stacks 0096 (blueprint: def-sfb-equivariant-tor-calculus-data). -/
def pullSection {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U) (s : Γ(M, U)) :
    Γ((Scheme.Modules.tensorPullback f).obj M, V) :=
  ((Scheme.Modules.tensorPullback f).obj M).presheaf.map (homOfLE h).op
    (Scheme.Modules.tensorPullbackSection f M U s)

/-- The ordinary tensor of sheaf modules, using the recorded localization tensor.
Source: Stacks 01CA (blueprint: def-sfb-equivariant-tor-calculus-data). -/
abbrev ordinaryTensor {X : Scheme.{u}} (P M : X.Modules) : X.Modules :=
  EquivariantCoherent.moduleTensor P M

/-- Simultaneously chosen affine comparisons and flat comparisons, with functoriality
and normalization on every augmented resolution. This is conclusion data: none of
these isomorphisms is an additional hypothesis of the existence theorem.
Source: Stacks 08BP, 00M8 and 01HV
(blueprint: def-sfb-equivariant-tor-calculus-data). -/
structure FlatCalculus where
  /-- Coherence of the actual derived Tor sheaf. -/
  coherent : ∀ (X : Space F) (q : ℕ) (P M : Coh X.val.left),
    RingedSpace.IsCoherent X.val.left.toRingedSpace (obj q P.val M.val)
  /-- Flat pullback preserves the coherent inputs. -/
  coherentPullback : ∀ {X Y : Space F} (f : X.val ⟶ Y.val) [Flat f.left]
    (P : Coh Y.val.left), RingedSpace.IsCoherent X.val.left.toRingedSpace
      ((Scheme.Modules.tensorPullback f.left).obj P.val)
  /-- The natural affine sections identification. -/
  affine : ∀ (X : Space F) (q : ℕ) (P M : Coh X.val.left) (U : X.val.left.affineOpens),
    sections (obj q P.val M.val) U.val ≅ ringTor q P.val M.val U.val
  /-- Naturality of the affine identification in both variables. -/
  affine_naturality : ∀ (X : Space F) (q : ℕ) (P P' M M' : Coh X.val.left)
    (f : P.val ⟶ P'.val) (g : M.val ⟶ M'.val) (U : X.val.left.affineOpens),
    (map q f g).val.app (op U.val) ≫ (affine X q P' M' U).hom =
      (affine X q P M U).hom ≫
        ((Tor' (ModuleCat Γ(X.val.left, U.val)) q).map
          (f.val.app (op U.val))).app (sections M.val U.val) ≫
        ((Tor' (ModuleCat Γ(X.val.left, U.val)) q).obj
          (sections P'.val U.val)).map (g.val.app (op U.val))
  /-- Flat comparison on the actual Tor objects. -/
  beta : ∀ {X Y : Space F} (f : X.val ⟶ Y.val) [Flat f.left]
    (q : ℕ) (P M : Coh Y.val.left),
    (Scheme.Modules.tensorPullback f.left).obj (obj q P.val M.val) ≅
      obj q ((Scheme.Modules.tensorPullback f.left).obj P.val)
        ((Scheme.Modules.tensorPullback f.left).obj M.val)
  /-- Naturality includes ordinary, possibly nonequivariant, input maps. -/
  beta_naturality : ∀ {X Y : Space F} (f : X.val ⟶ Y.val) [Flat f.left]
    (q : ℕ) (P P' M M' : Coh Y.val.left) (a : P.val ⟶ P'.val) (b : M.val ⟶ M'.val),
    (Scheme.Modules.tensorPullback f.left).map (map q a b) ≫ (beta f q P' M').hom =
      (beta f q P M).hom ≫ map q
        ((Scheme.Modules.tensorPullback f.left).map a)
        ((Scheme.Modules.tensorPullback f.left).map b)
  /-- Identity compatibility uses the section-normalized pullback identity. -/
  beta_id : ∀ (X : Space F) (q : ℕ) (P M : Coh X.val.left),
    (@beta X X (𝟙 X.val) (by
      change Flat (𝟙 X.val.left)
      infer_instance) q P M).hom ≫ map q
        ((Scheme.Modules.tensorPullbackSectionId X.val.left).hom.app P.val)
        ((Scheme.Modules.tensorPullbackSectionId X.val.left).hom.app M.val) =
      (Scheme.Modules.tensorPullbackSectionId X.val.left).hom.app (obj q P.val M.val)
  /-- Composition compatibility uses the section-normalized pullback compositor. -/
  beta_comp : ∀ {X Y Z : Space F} (f : X.val ⟶ Y.val) (g : Y.val ⟶ Z.val)
    [Flat f.left] [Flat g.left] (q : ℕ) (P M : Coh Z.val.left),
    (@beta X Z (f ≫ g) (Flat.comp f.left g.left) q P M).hom ≫ map q
        ((Scheme.Modules.tensorPullbackSectionComp f.left g.left).hom.app P.val)
        ((Scheme.Modules.tensorPullbackSectionComp f.left g.left).hom.app M.val) =
      (Scheme.Modules.tensorPullbackSectionComp f.left g.left).hom.app
          (obj q P.val M.val) ≫
        (Scheme.Modules.tensorPullback f.left).map (beta g q P M).hom ≫
        (beta f q
          ⟨_, coherentPullback g P⟩ ⟨_, coherentPullback g M⟩).hom



/-- A normalized flat comparison induces precisely the specified action linearization.
Source: Stacks 03LF, 08BP and 079U
(blueprint: def-sfb-equivariant-tor-calculus-data). -/
structure ActionCalculus (B : FlatCalculus F) where
  /-- The action product remains a finite-type scheme. -/
  productFinite : ∀ (G X : Space F),
    LocallyOfFiniteType (G.val ⊗ X.val).hom ∧ QuasiCompact (G.val ⊗ X.val).hom
  /-- The chosen action groupoid has the actual multiplication coordinate. -/
  groupoid : ∀ (G : Space F) [GrpObj G.val] [IsAffine G.val.left]
    (X : Space F) [ModObj G.val X.val], EquivariantCoherent.ActionGroupoidModel G.val X.val
  /-- Projection is flat over the field, including nonreduced groups. -/
  projectionFlat : ∀ (G X : Space F), Flat (EquivariantCoherent.source G.val X.val)
  /-- Action is projection after the inverse-coordinate automorphism. -/
  actionFlat : ∀ (G : Space F) [GrpObj G.val] (X : Space F) [ModObj G.val X.val],
    Flat (EquivariantCoherent.target G.val X.val)
  /-- The three face maps of composable action arrows are flat. Higher faces are
  their base changes and composites; the unit degeneracy is not included. -/
  faceFlat : ∀ (G : Space F) [GrpObj G.val] [IsAffine G.val.left]
    (X : Space F) [ModObj G.val X.val]
    (D : EquivariantCoherent.ActionGroupoidModel G.val X.val),
    Flat D.comp ∧ Flat (pullback.fst (EquivariantCoherent.source G.val X.val)
      (EquivariantCoherent.target G.val X.val)) ∧
    Flat (pullback.snd (EquivariantCoherent.source G.val X.val)
      (EquivariantCoherent.target G.val X.val))
  /-- Coherent realizations of the fixed derived Tor objects. -/
  tor : ∀ (G : Space F) [GrpObj G.val] [IsAffine G.val.left]
    (X : Space F) [ModObj G.val X.val]
    (D : EquivariantCoherent.ActionGroupoidModel G.val X.val)
    (_q : ℕ) (_P _M : EquivariantCoherent.Coherent D), EquivariantCoherent.Coherent D
  /-- These are isomorphic to the actual derived homology sheaves. -/
  realization : ∀ (G : Space F) [GrpObj G.val] [IsAffine G.val.left]
    (X : Space F) [ModObj G.val X.val]
    (D : EquivariantCoherent.ActionGroupoidModel G.val X.val)
    (q : ℕ) (P M : EquivariantCoherent.Coherent D),
    EquivariantCoherent.underlying (tor G X D q P M) ≅
      obj q (EquivariantCoherent.underlying P) (EquivariantCoherent.underlying M)
  /-- The linearization is beta_a, then Tor of the input linearizations, then beta_pr2^-1.
  The unit and cocycle identities are part of the existing Coherent carrier. -/
  linearization_formula : ∀ (G : Space F) [GrpObj G.val] [IsAffine G.val.left]
    (X : Space F) [ModObj G.val X.val]
    (D : EquivariantCoherent.ActionGroupoidModel G.val X.val)
    (q : ℕ) (P M : EquivariantCoherent.Coherent D),
    (Scheme.Modules.tensorPullback (EquivariantCoherent.target G.val X.val)).map
        (realization G X D q P M).hom ≫
      (@B.beta ⟨G.val ⊗ X.val, productFinite G X⟩ X (ModObj.smul (M := G.val))
        (actionFlat G X) q ⟨_, P.property⟩ ⟨_, M.property⟩).hom ≫
      map q (EquivariantCoherent.linearization P).hom
        (EquivariantCoherent.linearization M).hom ≫
      (@B.beta ⟨G.val ⊗ X.val, productFinite G X⟩ X (snd G.val X.val)
        (projectionFlat G X) q ⟨_, P.property⟩ ⟨_, M.property⟩).inv =
      (EquivariantCoherent.linearization (tor G X D q P M)).hom ≫
        (Scheme.Modules.tensorPullback (EquivariantCoherent.source G.val X.val)).map
          (realization G X D q P M).hom
  /-- Tor maps in both variables lift to equivariant maps. -/
  maps : ∀ (G : Space F) [GrpObj G.val] [IsAffine G.val.left]
    (X : Space F) [ModObj G.val X.val]
    (D : EquivariantCoherent.ActionGroupoidModel G.val X.val)
    (q : ℕ) (P P' M M' : EquivariantCoherent.Coherent D) (f : P ⟶ P') (g : M ⟶ M'),
    ∃ t : tor G X D q P M ⟶ tor G X D q P' M',
      EquivariantCoherent.underlyingMap t ≫ (realization G X D q P' M').hom =
        (realization G X D q P M).hom ≫ map q
          (EquivariantCoherent.underlyingMap f) (EquivariantCoherent.underlyingMap g)

end AlgebraicGeometry.SchemeTor

namespace AlgebraicGeometry.SchemeTor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory.CartesianMonoidalCategory
open Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Additivity from the recorded pullback adjunction. Source: Stacks 0096
(blueprint: def-sfb-equivariant-tor-calculus-data). -/
local instance pullbackAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (tensorPullback f).Additive :=
  (tensorPullbackSectionAdjunction f).left_adjoint_additive

/-- The existing module tensor. Source: Stacks 01CA
(blueprint: def-sfb-equivariant-tor-calculus-data). -/
local instance modulesMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf

/-- Additivity of the existing module tensor. Source: Stacks 01CA
(blueprint: def-sfb-equivariant-tor-calculus-data). -/
local instance modulesMonoidalPreadditive (X : Scheme.{u}) :
    MonoidalPreadditive X.Modules :=
  (SheafOfModules.tensorClosed X.sheaf).1.some

variable (F : Type u) [Field F]

/-- Exactness of two consecutive sheaf arrows, in the abelian sheaf category.
Source: Stacks 08BP (blueprint: def-sfb-equivariant-tor-calculus-data). -/
def ExactPair {X : Scheme.{u}} {A B C : X.Modules} (f : A ⟶ B) (g : B ⟶ C) : Prop :=
  ∃ h : f ≫ g = 0, (ShortComplex.mk f g h).Exact

/-- A coherent equivariant kernel and image with their actual inclusions.
Source: Stacks 01BY and 03LF (blueprint: def-sfb-equivariant-tor-calculus-data). -/
def HasCoherentKernelImage {S : Scheme.{u}} {G X : Over S} [GrpObj G] [ModObj G X]
    {D : EquivariantCoherent.ActionGroupoidModel G X}
    {P M : EquivariantCoherent.Coherent D} (f : P ⟶ M) : Prop :=
  ∃ (K I : EquivariantCoherent.Coherent D) (k : K ⟶ P) (i : I ⟶ M)
    (eK : EquivariantCoherent.underlying K ≅ kernel (EquivariantCoherent.underlyingMap f))
    (eI : EquivariantCoherent.underlying I ≅ image (EquivariantCoherent.underlyingMap f)),
    EquivariantCoherent.underlyingMap k =
      eK.hom ≫ kernel.ι (EquivariantCoherent.underlyingMap f) ∧
    EquivariantCoherent.underlyingMap i =
      eI.hom ≫ image.ι (EquivariantCoherent.underlyingMap f)

set_option maxHeartbeats 100000 in
-- The comparison record binds several dependent sheaf and derived-category interfaces.
/-- The Tor long exact sequence, with its actual derived connecting morphisms,
including its degree-zero endpoint and coherent equivariant kernels and images.
Source: Stacks 08BP and 01BY (blueprint: def-sfb-equivariant-tor-calculus-data). -/
structure ExactCalculus (B : FlatCalculus F) (A : ActionCalculus F B) where
  /-- Flat pullback is exact on sheaf modules. -/
  flatExact : ∀ {X Y : Space F} (f : X.val ⟶ Y.val) [Flat f.left]
    (S : ShortComplex Y.val.left.Modules), S.ShortExact →
      (S.map (tensorPullback f.left)).ShortExact
  /-- Equivariance of the connecting morphism in the second variable. -/
  boundary_right : ∀ (G : Space F) [GrpObj G.val] [IsAffine G.val.left]
    (X : Space F) [ModObj G.val X.val]
    (D : EquivariantCoherent.ActionGroupoidModel G.val X.val)
    (P L M N : EquivariantCoherent.Coherent D) (f : L ⟶ M) (g : M ⟶ N)
    (h : EquivariantCoherent.underlyingMap f ≫ EquivariantCoherent.underlyingMap g = 0)
    (hs : (ShortComplex.mk (EquivariantCoherent.underlyingMap f)
      (EquivariantCoherent.underlyingMap g) h).ShortExact) (q : ℕ),
    ∃ d : A.tor G X D (q + 1) P N ⟶ A.tor G X D q P L,
      EquivariantCoherent.underlyingMap d ≫ (A.realization G X D q P L).hom =
        (A.realization G X D (q + 1) P N).hom ≫
          boundaryRight (EquivariantCoherent.underlying P) _ hs q ∧
      HasCoherentKernelImage (D := D) d
  /-- Equivariance of the connecting morphism in the first variable. -/
  boundary_left : ∀ (G : Space F) [GrpObj G.val] [IsAffine G.val.left]
    (X : Space F) [ModObj G.val X.val]
    (D : EquivariantCoherent.ActionGroupoidModel G.val X.val)
    (P L M N : EquivariantCoherent.Coherent D) (f : L ⟶ M) (g : M ⟶ N)
    (h : EquivariantCoherent.underlyingMap f ≫ EquivariantCoherent.underlyingMap g = 0)
    (hs : (ShortComplex.mk (EquivariantCoherent.underlyingMap f)
      (EquivariantCoherent.underlyingMap g) h).ShortExact) (q : ℕ),
    ∃ d : A.tor G X D (q + 1) N P ⟶ A.tor G X D q L P,
      EquivariantCoherent.underlyingMap d ≫ (A.realization G X D q L P).hom =
        (A.realization G X D (q + 1) N P).hom ≫
          boundaryLeft (EquivariantCoherent.underlying P) _ hs q ∧
      HasCoherentKernelImage (D := D) d
  /-- The Tor arrows themselves have coherent equivariant kernels and images. -/
  map_subobjects : ∀ (G : Space F) [GrpObj G.val] [IsAffine G.val.left]
    (X : Space F) [ModObj G.val X.val]
    (D : EquivariantCoherent.ActionGroupoidModel G.val X.val)
    (q : ℕ) (P P' M M' : EquivariantCoherent.Coherent D) (f : P ⟶ P') (g : M ⟶ M'),
    ∃ t : A.tor G X D q P M ⟶ A.tor G X D q P' M',
      EquivariantCoherent.underlyingMap t ≫ (A.realization G X D q P' M').hom =
        (A.realization G X D q P M).hom ≫ map q
          (EquivariantCoherent.underlyingMap f) (EquivariantCoherent.underlyingMap g) ∧
      HasCoherentKernelImage (D := D) t
  /-- All three kinds of adjacent arrows are exact, in both variables. -/
  exact : ∀ (X : Space F) (P : Coh X.val.left)
    (S : ShortComplex X.val.left.Modules) (hs : S.ShortExact)
    (_h : ∀ i : Fin 3, RingedSpace.IsCoherent X.val.left.toRingedSpace
      (if i = 0 then S.X₁ else if i = 1 then S.X₂ else S.X₃)) (q : ℕ),
    ExactPair (X := X.val.left)
      (map (X := X.val.left) q (𝟙 P.val) S.f) (map (X := X.val.left) q (𝟙 P.val) S.g) ∧
    ExactPair (X := X.val.left)
      (map (X := X.val.left) (q + 1) (𝟙 P.val) S.g) (boundaryRight P.val S hs q) ∧
    ExactPair (X := X.val.left)
      (boundaryRight P.val S hs q) (map (X := X.val.left) q (𝟙 P.val) S.f) ∧
    ExactPair (X := X.val.left)
      (map (X := X.val.left) q S.f (𝟙 P.val)) (map (X := X.val.left) q S.g (𝟙 P.val)) ∧
    ExactPair (X := X.val.left)
      (map (X := X.val.left) (q + 1) S.g (𝟙 P.val)) (boundaryLeft P.val S hs q) ∧
    ExactPair (X := X.val.left)
      (boundaryLeft P.val S hs q) (map (X := X.val.left) q S.f (𝟙 P.val)) ∧
    Epi (map (X := X.val.left) 0 (𝟙 P.val) S.g) ∧ Epi (map (X := X.val.left) 0 S.g (𝟙 P.val))
  /-- The degree-zero term is ordinary tensor, for all coherent inputs. -/
  zero : ∀ (X : Space F) (P M : Coh X.val.left),
    obj (X := X.val.left) 0 P.val M.val ≅ ordinaryTensor P.val M.val
  /-- Flat comparison commutes with the second-variable derived connecting morphism. -/
  beta_boundary_right : ∀ {X Y : Space F} (f : X.val ⟶ Y.val) [Flat f.left]
    (P L M N : Coh Y.val.left) (s : L.val ⟶ M.val) (t : M.val ⟶ N.val)
    (h : s ≫ t = 0) (hs : (ShortComplex.mk s t h).ShortExact) (q : ℕ),
    (tensorPullback f.left).map (boundaryRight P.val _ hs q) ≫
        (B.beta f q P L).hom =
      (B.beta f (q + 1) P N).hom ≫
        (letI := pullbackAdditive f.left; boundaryRight ((tensorPullback f.left).obj P.val)
          ((ShortComplex.mk s t h).map (tensorPullback f.left))
          (flatExact f _ hs) q)
  /-- The same compatibility in the first variable. -/
  beta_boundary_left : ∀ {X Y : Space F} (f : X.val ⟶ Y.val) [Flat f.left]
    (P L M N : Coh Y.val.left) (s : L.val ⟶ M.val) (t : M.val ⟶ N.val)
    (h : s ≫ t = 0) (hs : (ShortComplex.mk s t h).ShortExact) (q : ℕ),
    (tensorPullback f.left).map (boundaryLeft P.val _ hs q) ≫
        (B.beta f q L P).hom =
      (B.beta f (q + 1) N P).hom ≫
        (letI := pullbackAdditive f.left; boundaryLeft ((tensorPullback f.left).obj P.val)
          ((ShortComplex.mk s t h).map (tensorPullback f.left))
          (flatExact f _ hs) q)

/-- Finite free resolutions compute the fixed derived tensor, without requiring finite
length. The augmentation and comparison used are the actual ones above.
Source: Stacks 06YH and 08BP (blueprint: def-sfb-equivariant-tor-calculus-data). -/
def ResolutionCalculus : Prop :=
  ∀ (X : Space F)
    (E : CochainComplex (SheafOfModules.{u} (moduleRings X.val.left.toRingedSpace)) ℤ)
    (rank : ℤ → ℕ)
    (_e : ∀ i : ℤ, E.X i ≅
      SheafOfModules.free (R := X.val.left.ringCatSheaf) (ULift.{u} (Fin (rank i))))
    (_h : ∀ i : ℤ, 0 < i → IsZero (E.X i)), kFlat E

/-- Flat equivariant pullback exists in the existing coherent descent category.
Source: Stacks 03LF and 02N4 (blueprint: def-sfb-equivariant-tor-calculus-data). -/
def EquivariantPullbacks : Prop :=
  ∀ (G : Space F) [GrpObj G.val] [IsAffine G.val.left]
    (X Y : Space F) [ModObj G.val X.val] [ModObj G.val Y.val]
    (DX : EquivariantCoherent.ActionGroupoidModel G.val X.val)
    (DY : EquivariantCoherent.ActionGroupoidModel G.val Y.val)
    (f : X.val ⟶ Y.val) [Flat f.left] [IsModHom G.val f]
    (P : EquivariantCoherent.Coherent DY),
    ∃ P' : EquivariantCoherent.Coherent DX, EquivariantCoherent.IsPullback f P P'

/-- The flat comparison is equivariant for every equivariant flat morphism, with
specified pullback realizations of the two inputs.
Source: Stacks 03LF and 00M8 (blueprint: def-sfb-equivariant-tor-calculus-data). -/
def EquivariantFlatCalculus (B : FlatCalculus F) (A : ActionCalculus F B) : Prop :=
  ∀ (G : Space F) [GrpObj G.val] [IsAffine G.val.left]
    (X Y : Space F) [ModObj G.val X.val] [ModObj G.val Y.val]
    (DX : EquivariantCoherent.ActionGroupoidModel G.val X.val)
    (DY : EquivariantCoherent.ActionGroupoidModel G.val Y.val)
    (f : X.val ⟶ Y.val) [Flat f.left] [IsModHom G.val f]
    (q : ℕ) (P M : EquivariantCoherent.Coherent DY)
    (P' M' : EquivariantCoherent.Coherent DX)
    (eP : (tensorPullback f.left).obj (EquivariantCoherent.underlying P) ≅
      EquivariantCoherent.underlying P')
    (eM : (tensorPullback f.left).obj (EquivariantCoherent.underlying M) ≅
      EquivariantCoherent.underlying M'),
    EquivariantCoherent.IsPullbackMap f P P' eP.hom →
    EquivariantCoherent.IsPullbackMap f M M' eM.hom →
    let comparison :=
      (tensorPullback f.left).map (A.realization G Y DY q P M).hom ≫
        (B.beta f q ⟨_, P.property⟩ ⟨_, M.property⟩).hom ≫ map q eP.hom eM.hom ≫
        (A.realization G X DX q P' M').inv
    IsIso comparison ∧
    EquivariantCoherent.IsPullbackMap f (A.tor G Y DY q P M) (A.tor G X DX q P' M')
      ((tensorPullback f.left).map (A.realization G Y DY q P M).hom ≫
        (B.beta f q ⟨_, P.property⟩ ⟨_, M.property⟩).hom ≫ map q eP.hom eM.hom ≫
        (A.realization G X DX q P' M').inv)

end AlgebraicGeometry.SchemeTor

namespace AlgebraicGeometry.SchemeTor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


open Scheme.Modules
attribute [local instance] pullbackAdditive modulesMonoidal modulesMonoidalPreadditive
open CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct

variable (F : Type u) [Field F]

set_option maxHeartbeats 100000 in
-- The comparison record binds several dependent sheaf and derived-category interfaces.
/-- The canonical affine base-change formula on every augmented projective resolution.
A lift of the section pullback and its tensor lift determine the map on cycles; this
pins beta to the usual flat base-change isomorphism, including open restrictions.
Source: Stacks 00M8 and 00LS (blueprint: def-sfb-equivariant-tor-calculus-data). -/
def AffineBaseChangeCalculus (B : FlatCalculus F) : Prop :=
  ∀ {X Y : Space F} (f : X.val ⟶ Y.val) [Flat f.left] (q : ℕ)
    (P M : Coh Y.val.left) (U : Y.val.left.affineOpens) (V : X.val.left.affineOpens)
    (h : V.val ≤ f.left ⁻¹ᵁ U.val),
    let P' : Coh X.val.left := ⟨_, B.coherentPullback f P⟩
    let M' : Coh X.val.left := ⟨_, B.coherentPullback f M⟩
    let R := ModuleCat.restrictScalars (f.left.appLE U.val V.val h).hom
    ∀ (E : ProjectiveResolution (sections P.val U.val))
      (E' : ProjectiveResolution (sections P'.val V.val))
      (c : E.complex ⟶ (R.mapHomologicalComplex (.down ℕ)).obj E'.complex),
      (∀ e : E.complex.X 0,
        (E'.π.f 0).hom ((c.f 0).hom e) =
          pullSection f.left P.val U.val V.val h ((E.π.f 0).hom e)) →
      ∀ (t : ringComplex P.val M.val U.val E ⟶
        (R.mapHomologicalComplex (.down ℕ)).obj (ringComplex P'.val M'.val V.val E')),
        (∀ (j : ℕ) (e : E.complex.X j) (m : sections M.val U.val),
          (t.f j).hom (e ⊗ₜ[Γ(Y.val.left, U.val)] m) =
            (show E'.complex.X j from (c.f j).hom e) ⊗ₜ[Γ(X.val.left, V.val)]
              pullSection f.left M.val U.val V.val h m) →
        ∀ (z : (ringComplex P.val M.val U.val E).cycles q)
          (z' : (ringComplex P'.val M'.val V.val E').cycles q),
          (t.f q).hom ((ringComplex P.val M.val U.val E).iCycles q |>.hom z) =
            ((ringComplex P'.val M'.val V.val E').iCycles q).hom z' →
          ∀ b : Γ(X.val.left, V.val),
            (B.affine X q P' M' V).hom.hom
              ((B.beta f q P M).hom.app V.val
                (b • pullSection f.left (obj q P.val M.val) U.val V.val h
                  ((B.affine Y q P M U).inv.hom
                    ((ringResolutionIso q P.val M.val U.val E).inv.hom
                      (((ringComplex P.val M.val U.val E).homologyπ q).hom z))))) =
              b • (ringResolutionIso q P'.val M'.val V.val E').inv.hom
                (((ringComplex P'.val M'.val V.val E').homologyπ q).hom z')

set_option maxHeartbeats 100000 in
-- The comparison record binds several dependent sheaf and derived-category interfaces.
/-- The reassociation map of the termwise tensor complexes, obtained from the actual
monoidal associator, before taking homology.
Source: Stacks 08BP (blueprint: def-sfb-equivariant-tor-calculus-data). -/
def reassociate {X : Scheme.{u}}
    (E : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (M V : X.Modules) :
    tensorComplex (tensorComplex E M) V ≅ tensorComplex E (ordinaryTensor M V) :=
  (Functor.mapHomologicalComplexCompIso
    (tensorRightTensor (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)) M V).symm
    (.up ℤ)).app E

/-- The Tor reassociation map is the map induced by termwise reassociation on cycles.
Source: Stacks 08BP (blueprint: def-sfb-equivariant-tor-calculus-data). -/
def IsTensorComparison {X : Scheme.{u}} (P M V : X.Modules) (q : ℕ)
    (t : ordinaryTensor (obj q P M) V ⟶ obj q P (ordinaryTensor M V)) : Prop :=
  ∀ (E : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (a : E ⟶ (HomologicalComplex.single
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ) 0).obj P)
    [QuasiIso a] (hk : kFlat E),
    let C := tensorComplex E M
    let C' := tensorComplex E (ordinaryTensor M V)
    ∀ (U : X.Opens) (z : Γ(C.cycles (-(q : ℤ)), U)) (v : Γ(V, U))
      (w : Γ(C'.cycles (-(q : ℤ)), U)),
      (C'.iCycles (-(q : ℤ))).val.app (op U) w =
        ((reassociate E M V).hom.f (-(q : ℤ))).val.app (op U)
          (tmulSection ((C.iCycles (-(q : ℤ))).val.app (op U) z) v) →
      (t ≫ (resolutionHomologyIso (X := X) P (ordinaryTensor M V) q E a hk).hom).app U
        (tmulSection ((resolutionHomologyIso (X := X) P M q E a hk).inv.app U
          ((C.homologyπ (-(q : ℤ))).val.app (op U) z)) v) =
        (C'.homologyπ (-(q : ℤ))).val.app (op U) w

set_option maxHeartbeats 100000 in
-- The comparison record binds several dependent sheaf and derived-category interfaces.
/-- Finite locally free tensor exactness and equivariant Tor tensor comparison.
The normalization on cycles specifies the associativity comparison, including rank zero.
Source: Stacks 08BP and 06YH (blueprint: def-sfb-equivariant-tor-calculus-data). -/
structure LocallyFreeCalculus (B : FlatCalculus F) (A : ActionCalculus F B) where
  /-- Finite local ranks may vary between trivializing opens. -/
  exactTensor : ∀ (X : Space F) (V : X.val.left.Modules) [V.IsFiniteLocallyFree],
    PreservesFiniteLimits
      (tensorRight (C := SheafOfModules.{u} (moduleRings X.val.left.toRingedSpace)) V) ∧
    PreservesFiniteColimits
      (tensorRight (C := SheafOfModules.{u} (moduleRings X.val.left.toRingedSpace)) V)
  /-- The tensor comparison, with both tensors carrying the induced linearization. -/
  tensor : ∀ (G : Space F) [GrpObj G.val] [IsAffine G.val.left]
    (X : Space F) [ModObj G.val X.val]
    (D : EquivariantCoherent.ActionGroupoidModel G.val X.val)
    (q : ℕ) (P M V : EquivariantCoherent.Coherent D)
    [SheafOfModules.IsFiniteLocallyFree
      (R := moduleRings X.val.left.toRingedSpace) (EquivariantCoherent.underlying V)],
    ∃ (N K : EquivariantCoherent.Coherent D)
      (eN : EquivariantCoherent.underlying N ≅ ordinaryTensor (X := X.val.left)
        (EquivariantCoherent.underlying M) (EquivariantCoherent.underlying V))
      (eK : EquivariantCoherent.underlying K ≅ ordinaryTensor (X := X.val.left)
        (EquivariantCoherent.underlying (A.tor G X D q P M))
        (EquivariantCoherent.underlying V))
      (e : K ≅ A.tor G X D q P N),
      ((Scheme.Modules.tensorPullback (EquivariantCoherent.target G.val X.val)).map
          eN.hom ≫
        (EquivariantCoherent.tensorComparison (EquivariantCoherent.target G.val X.val)
          (EquivariantCoherent.underlying M) (EquivariantCoherent.underlying V)).hom ≫
        EquivariantCoherent.moduleTensorMap (EquivariantCoherent.linearization M).hom
          (EquivariantCoherent.linearization V).hom =
        (EquivariantCoherent.linearization N).hom ≫
          (Scheme.Modules.tensorPullback (EquivariantCoherent.source G.val X.val)).map
            eN.hom ≫
          (EquivariantCoherent.tensorComparison (EquivariantCoherent.source G.val X.val)
            (EquivariantCoherent.underlying M) (EquivariantCoherent.underlying V)).hom) ∧
      ((Scheme.Modules.tensorPullback (EquivariantCoherent.target G.val X.val)).map
          eK.hom ≫
        (EquivariantCoherent.tensorComparison (EquivariantCoherent.target G.val X.val)
          (EquivariantCoherent.underlying (A.tor G X D q P M))
            (EquivariantCoherent.underlying V)).hom ≫
        EquivariantCoherent.moduleTensorMap
          (EquivariantCoherent.linearization (A.tor G X D q P M)).hom
          (EquivariantCoherent.linearization V).hom =
        (EquivariantCoherent.linearization K).hom ≫
          (Scheme.Modules.tensorPullback (EquivariantCoherent.source G.val X.val)).map
            eK.hom ≫
          (EquivariantCoherent.tensorComparison (EquivariantCoherent.source G.val X.val)
            (EquivariantCoherent.underlying (A.tor G X D q P M))
            (EquivariantCoherent.underlying V)).hom) ∧
      IsTensorComparison (X := X.val.left) (EquivariantCoherent.underlying P)
        (EquivariantCoherent.underlying M) (EquivariantCoherent.underlying V) q
        (EquivariantCoherent.moduleTensorMap (A.realization G X D q P M).inv
          (𝟙 (EquivariantCoherent.underlying V)) ≫ eK.inv ≫
          EquivariantCoherent.underlyingMap (D := D) e.hom ≫
          (A.realization G X D q P N).hom ≫
          map (X := X.val.left) q (𝟙 (EquivariantCoherent.underlying P)) eN.hom)
  /-- Degree zero and every strictly positive degree for a finite locally free input. -/
  flat_input : ∀ (X : Space F) (P V : Coh X.val.left) [V.val.IsFiniteLocallyFree],
    Nonempty (obj (X := X.val.left) 0 P.val V.val ≅ ordinaryTensor (X := X.val.left) P.val V.val) ∧
      ∀ q : ℕ, 0 < q → IsZero (obj (X := X.val.left) q P.val V.val)

end AlgebraicGeometry.SchemeTor
