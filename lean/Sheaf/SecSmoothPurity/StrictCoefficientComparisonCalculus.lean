/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.CategoryTheory.SystemScalarCoherence
public import Mathlib.CategoryTheory.Products.Basic

/-! # Simultaneous strict coefficient comparisons

Source: Stacks 03EL and 07A4; the agent calculations in the eight proof steps of
lem-pur-strict-coefficient-comparison-calculus
(blueprint: lem-pur-strict-coefficient-comparison-calculus).

The product index records coefficient changes and all inverse-sequence arrows.
Semilinear arrows are written in their scalar-extension adjoint form. Thus they
are arbitrary chain maps out of scalar extension, including zero maps, rather
than only the scalar-extension units. All tensors are the existing sheafified
module tensor and its signed direct-sum total complex.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] SheafOfModules.monoidalCategory
set_option maxErrors 5
universe w uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace CategoryTheory.CochainPullback.StrictCoefficient

/-- Three coefficient rows and an inverse sequence, with all iterated arrows.
Source: the item's statement (blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
abbrev Index := Fin 3 × ℕᵒᵖ

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The existing signed direct-sum total tensor, with its instances fixed once.
Source: Stacks 07A4 (blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
abbrev total {R : Sheaf J CommRingCat.{w}} (P Q : Complex R) : Complex R := P ⊗ Q

/-- The existing tensor map on total complexes, with its instances fixed once.
Source: Stacks 07A4 (blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
abbrev totalMap {R : Sheaf J CommRingCat.{w}} {P Q P' Q' : Complex R}
    (f : P ⟶ P') (g : Q ⟶ Q') : total P Q ⟶ total P' Q' := f ⊗ₘ g

/-- The existing tensor isomorphism on total complexes, with instances fixed once.
Source: Stacks 07A4 (blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
abbrev totalIso {R : Sheaf J CommRingCat.{w}} {P Q P' Q' : Complex R}
    (f : P ≅ P') (g : Q ≅ Q') : total P Q ≅ total P' Q' := f ⊗ᵢ g

/-- Presentation of precisely the ring diagrams in the statement. The fields L,
hobj and hmap present actual scalar extension after the algebraic inverse image;
they are not extra operations or flatness assumptions. The common set adjunction
and the graph equation say that every arrow uses the same geometric morphism.
Source: Stacks 03EL and 07A4
(blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
structure Diagram where
  R : Index ⥤ Sheaf J CommRingCat.{w}
  S : Index ⥤ Sheaf K CommRingCat.{w}
  RI : Index ⥤ Sheaf K CommRingCat.{w}
  phi : RI ⟶ S
  inverse : Sheaf J (Type w) ⥤ Sheaf K (Type w)
  direct : Sheaf K (Type w) ⥤ Sheaf J (Type w)
  adj : inverse ⊣ direct
  finiteLimits : PreservesFiniteLimits inverse
  algebraic : ∀ i : Index, SheafOfModules.AlgebraicInverseImage inverse (R.obj i) (RI.obj i)
  graph : ∀ {i j : Index} (t : i ⟶ j),
    inverse.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map (R.map t)) ≫
        (algebraic j).ringUnderlying.hom =
      (algebraic i).ringUnderlying.hom ≫
        (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map (RI.map t)
  L : ∀ i : Index, Modules (R.obj i) ⥤ Modules (S.obj i)
  hobj : ∀ (i : Index) (M : Modules (R.obj i)),
    (L i).obj M = SheafOfModules.changeOfRings (phi.app i) ((algebraic i).modules.obj M)
  hmap : ∀ (i : Index) {M N : Modules (R.obj i)} (f : M ⟶ N),
    (L i).map f = eqToHom (hobj i M) ≫
      SheafOfModules.changeOfRingsHom (phi.app i) ((algebraic i).modules.obj M)
        ((algebraic i).modules.map f) ≫ eqToHom (hobj i N).symm
  V : ∀ i : Index, Modules (S.obj i) ⥤ Modules (R.obj i)
  moduleAdj : ∀ i : Index, L i ⊣ V i
  additive : ∀ i : Index, (L i).Additive

attribute [instance] Diagram.additive

variable (d : Diagram (J := J) (K := K))

/-- The recorded ringed pullback at a coefficient and sequence level.
Source: Stacks 03EL (blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
def Diagram.ringed (i : Index) : RingedPullback (d.R.obj i) (d.S.obj i) where
  uInv := d.inverse
  uPush := d.direct
  adj := d.adj
  finiteLimits := d.finiteLimits
  RI := d.RI.obj i
  I := d.algebraic i
  coefficient := d.phi.app i
  L := d.L i
  hobj := d.hobj i
  hmap := d.hmap i
  V := d.V i
  moduleAdj := d.moduleAdj i
  additive := d.additive i

/-- Every coefficient or sequence arrow is the existing coefficient square.
Source: Stacks 03EL (blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
def Diagram.square {i j : Index} (t : i ⟶ j) : CoefficientSquare (d.ringed i) where
  R' := d.R.obj j
  S' := d.S.obj j
  sourceMap := d.R.map t
  targetMap := d.S.map t
  RI' := d.RI.obj j
  I' := d.algebraic j
  coefficient' := d.phi.app j
  inverseImageMap := d.RI.map t
  inverseImageMap_graph := d.graph t
  square := d.phi.naturality t
  L' := d.L j
  hobj' := d.hobj j
  hmap' := d.hmap j
  V' := d.V j
  moduleAdj' := d.moduleAdj j
  additive' := d.additive j

/-- Cochain scalar-extension composition, using the existing identity-on-sections
restriction comparison and adjoint uniqueness; no arbitrary associator is chosen.
Source: Stacks 03CY, 03EL
(blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
def scalarComp {A B H : Sheaf J CommRingCat.{w}}
    (a : A ⟶ B) (b : B ⟶ H) (c : A ⟶ H) (hc : c = a ≫ b) :
    extend a ⋙ extend b ≅ extend c :=
  NatIso.mapHomologicalComplex
    (Adjunction.leftAdjointUniq
      (((extensionAdjunction a).comp (extensionAdjunction b)).ofNatIsoRight
        (SheafOfModules.systemScalarRestrictionComposition a b c hc))
      (extensionAdjunction c)) (.up ℤ)

/-- Cochain action unit for scalar extension along an identity ring map.
Source: Stacks 03CY, 03EL
(blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
def scalarUnit (A : Sheaf J CommRingCat.{w}) : extend (𝟙 A) ≅ 𝟭 (Complex A) :=
  NatIso.mapHomologicalComplex
    (Adjunction.leftAdjointUniq
      ((extensionAdjunction (𝟙 A)).ofNatIsoRight
        (SheafOfModules.systemScalarRestrictionUnit (𝟙 A) rfl)) Adjunction.id) (.up ℤ)

/-- Canonical associator along two arrows of a ring diagram.
Source: Stacks 03EL (blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
def diagramComp (B : Index ⥤ Sheaf J CommRingCat.{w})
    {i j k : Index} (a : i ⟶ j) (b : j ⟶ k) :
    extend (B.map a) ⋙ extend (B.map b) ≅ extend (B.map (a ≫ b)) :=
  scalarComp (B.map a) (B.map b) (B.map (a ≫ b)) (B.map_comp a b)

/-- Canonical unit along the identity arrow of a ring diagram.
Source: Stacks 03EL (blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
def diagramUnit (B : Index ⥤ Sheaf J CommRingCat.{w}) (i : Index) :
    extend (B.map (𝟙 i)) ≅ 𝟭 (Complex (B.obj i)) :=
  eqToIso (congrArg (fun f ↦ extend f) (B.map_id i)) ≪≫ scalarUnit (B.obj i)

/-- Simultaneous module comparisons. Each sigma is the existing normalized
comparison type: its naturality and generalized pure-tensor formula are fields.
Kappa is a natural isomorphism; its generator normalization is stated separately.
Source: Stacks 03EL (blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
structure Comparisons where
  kappa : ∀ {i j : Index} (t : i ⟶ j),
    d.L i ⋙ extensionFunctor (d.S.map t) ≅ extensionFunctor (d.R.map t) ⋙ d.L j
  sigmaR : ∀ {i j : Index} (t : i ⟶ j), Comparison (extensionPullback (d.R.map t))
  sigmaS : ∀ {i j : Index} (t : i ⟶ j), Comparison (extensionPullback (d.S.map t))

variable {d}

/-- The generalized-generator equation fixes the displayed kappa formulas in
both directions: by linearity and balancing it is exactly
b tensor (a tensor x) mapped to b i(a) tensor (1 tensor x).
The inverse is forced by the isomorphism law and multiplies by phi(d).
Source: Stacks 03EL (blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
def Comparisons.Normalized (e : Comparisons d)
    (k : ∀ i : Index, Comparison (d.ringed i)) : Prop :=
  ∀ {i j : Index} (t : i ⟶ j),
    IsScalarAssociation (d.ringed i) (k i) (d.square t) (k j) (e.kappa t).symm

/-- The termwise cochain lift of kappa, retaining the underlying natural isomorphism.
Source: Stacks 03EL and 07A4
(blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
def Comparisons.kappaC (e : Comparisons d) {i j : Index} (t : i ⟶ j)
    (P : Complex (d.R.obj i)) :
    (extend (d.S.map t)).obj ((pull (d.ringed i)).obj P) ≅
      (pull (d.ringed j)).obj ((extend (d.R.map t)).obj P) :=
  (NatIso.mapHomologicalComplex (e.kappa t) (.up ℤ)).app P

/-- Sigma on unbounded total tensors over Y, with its normalized inverse.
Source: Stacks 03EL and 07A4
(blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
def Comparisons.sigmaRC (e : Comparisons d) {i j : Index} (t : i ⟶ j)
    (P Q : Complex (d.R.obj i)) :
    (extend (d.R.map t)).obj (total P Q) ≅
      total ((extend (d.R.map t)).obj P) ((extend (d.R.map t)).obj Q) :=
  comparison (extensionPullback (d.R.map t)) (e.sigmaR t) P Q

/-- Sigma on unbounded total tensors over X, with its normalized inverse.
Source: Stacks 03EL and 07A4
(blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
def Comparisons.sigmaSC (e : Comparisons d) {i j : Index} (t : i ⟶ j)
    (P Q : Complex (d.S.obj i)) :
    (extend (d.S.map t)).obj (total P Q) ≅
      total ((extend (d.S.map t)).obj P) ((extend (d.S.map t)).obj Q) :=
  comparison (extensionPullback (d.S.map t)) (e.sigmaS t) P Q

/-- The actual induced pullback of an arbitrary semilinear chain map, expressed
by its scalar-extension adjoint. This permits every strict-system transition,
including zero transitions and maps not invertible after scalar extension.
Source: Stacks 03CY and 03EL
(blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
def Comparisons.pullArrow (e : Comparisons d) {i j : Index} (t : i ⟶ j)
    (P : Complex (d.R.obj i)) (Q : Complex (d.R.obj j))
    (f : (extend (d.R.map t)).obj P ⟶ Q) :
    (extend (d.S.map t)).obj ((pull (d.ringed i)).obj P) ⟶
      (pull (d.ringed j)).obj Q :=
  (e.kappaC t P).hom ≫ (pull (d.ringed j)).map f

/-- The tensor of two arbitrary semilinear transitions over Y.
Source: Stacks 03EL and 07A4
(blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
def Comparisons.tensorArrow (e : Comparisons d) {i j : Index} (t : i ⟶ j)
    (P Q : Complex (d.R.obj i)) (P' Q' : Complex (d.R.obj j))
    (f : (extend (d.R.map t)).obj P ⟶ P')
    (g : (extend (d.R.map t)).obj Q ⟶ Q') :
    (extend (d.R.map t)).obj (total P Q) ⟶ total P' Q' :=
  (e.sigmaRC t P Q).hom ≫ (totalMap f g)

/-- Transport an arbitrary semilinear transition across a commuting square of
coefficient and sequence arrows, using the canonical scalar associators.
Source: Stacks 03CY, 03EL, and the item's proof step 5
(blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
def squareArrow (B : Index ⥤ Sheaf J CommRingCat.{w})
    {i j k l : Index} (a : i ⟶ j) (b : k ⟶ l) (r : i ⟶ k) (s : j ⟶ l)
    (h : a ≫ s = r ≫ b) (P : Complex (B.obj i)) (Q : Complex (B.obj k))
    (f : (extend (B.map r)).obj P ⟶ Q) :
    (extend (B.map s)).obj ((extend (B.map a)).obj P) ⟶
      (extend (B.map b)).obj Q :=
  (diagramComp B a s).hom.app P ≫
    eqToHom (congrArg (fun t ↦ (extend (B.map t)).obj P) h) ≫
      (diagramComp B r b).inv.app P ≫ (extend (B.map b)).map f

/-- Tensoring arbitrary semilinear transitions after scalar extension.
Source: Stacks 03EL and 07A4
(blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
def tensorArrowFor (B : Index ⥤ Sheaf J CommRingCat.{w})
    (s : ∀ {i j : Index} (t : i ⟶ j), Comparison (extensionPullback (B.map t)))
    {i j : Index} (t : i ⟶ j)
    (P Q : Complex (B.obj i)) (P' Q' : Complex (B.obj j))
    (f : (extend (B.map t)).obj P ⟶ P') (g : (extend (B.map t)).obj Q ⟶ Q') :
    (extend (B.map t)).obj (total P Q) ⟶ total P' Q' :=
  (comparison (extensionPullback (B.map t)) (s t) P Q).hom ≫ (totalMap f g)

/-- The coefficient tensor comparisons commute with every strict transition.
The transitions f and g are arbitrary scalar-extension adjoints, not assumed
invertible or equal to extension units. The inverse sigma square is equivalent,
by cancelling the displayed isomorphisms.
Source: Stacks 03EL and 07A4, and the item's proof steps 4--5
(blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
def TensorTransitionLaws (B : Index ⥤ Sheaf J CommRingCat.{w})
    (z : ∀ {i j : Index} (t : i ⟶ j), Comparison (extensionPullback (B.map t))) : Prop :=
  ∀ {i j k l : Index} (a : i ⟶ j) (b : k ⟶ l) (r : i ⟶ k) (s : j ⟶ l)
    (h : a ≫ s = r ≫ b) (P Q : Complex (B.obj i)) (P' Q' : Complex (B.obj k))
    (f : (extend (B.map r)).obj P ⟶ P') (g : (extend (B.map r)).obj Q ⟶ Q'),
    (extend (B.map s)).map
        (comparison (extensionPullback (B.map a)) (z a) P Q).hom ≫
      (comparison (extensionPullback (B.map s)) (z s)
        ((extend (B.map a)).obj P) ((extend (B.map a)).obj Q)).hom ≫
      (totalMap (squareArrow B a b r s h P P' f) (squareArrow B a b r s h Q Q' g)) =
    squareArrow B a b r s h (total P Q) (total P' Q')
        (tensorArrowFor B z r P Q P' Q' f g) ≫
      (comparison (extensionPullback (B.map b)) (z b) P' Q').hom

/-- The coefficient pullback comparisons commute with every strict transition.
Both sides use actual scalar extension and the same arbitrary semilinear input
map; inverse kappa commutes too by cancelling the isomorphisms.
Source: Stacks 03EL and 07A4, and the item's proof steps 2 and 5
(blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
def Comparisons.KappaTransitionLaws (e : Comparisons d) : Prop :=
  ∀ {i j k l : Index} (a : i ⟶ j) (b : k ⟶ l) (r : i ⟶ k) (s : j ⟶ l)
    (h : a ≫ s = r ≫ b) (P : Complex (d.R.obj i)) (Q : Complex (d.R.obj k))
    (f : (extend (d.R.map r)).obj P ⟶ Q),
    (extend (d.S.map s)).map (e.kappaC a P).hom ≫
        e.pullArrow s ((extend (d.R.map a)).obj P) ((extend (d.R.map b)).obj Q)
          (squareArrow d.R a b r s h P Q f) =
      squareArrow d.S a b r s h ((pull (d.ringed i)).obj P) ((pull (d.ringed k)).obj Q)
          (e.pullArrow r P Q f) ≫ (e.kappaC b Q).hom

/-- Unit and successive-extension equations for a normalized tensor comparison.
They are equations of isomorphisms, so equality in both inverse directions is
included. Component isomorphisms are the usual chain isomorphisms with the
signed direct-sum differential; their naturality covers arbitrary chain maps.
Source: Stacks 03EL and 07A4, and the item's proof steps 7--8
(blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
def TensorLaws (B : Index ⥤ Sheaf J CommRingCat.{w})
    (s : ∀ {i j : Index} (t : i ⟶ j), Comparison (extensionPullback (B.map t))) : Prop :=
  (∀ (i : Index) (P Q : Complex (B.obj i)),
    comparison (extensionPullback (B.map (𝟙 i))) (s (𝟙 i)) P Q ≪≫
        (totalIso ((diagramUnit B i).app P) ((diagramUnit B i).app Q)) =
      (diagramUnit B i).app (total P Q)) ∧
  (∀ {i j k : Index} (a : i ⟶ j) (b : j ⟶ k) (P Q : Complex (B.obj i)),
    (extend (B.map b)).mapIso
        (comparison (extensionPullback (B.map a)) (s a) P Q) ≪≫
      comparison (extensionPullback (B.map b)) (s b)
        ((extend (B.map a)).obj P) ((extend (B.map a)).obj Q) ≪≫
      (totalIso ((diagramComp B a b).app P) ((diagramComp B a b).app Q)) =
    (diagramComp B a b).app (total P Q) ≪≫
      comparison (extensionPullback (B.map (a ≫ b))) (s (a ≫ b)) P Q)

/-- Every square, unit and composition equation, including arbitrary semilinear
sequence transitions. The product index makes the successive coefficient
arrows 01,12,02 and every sequence map instances of these same equations.
Source: Stacks 03EL and 07A4, and all eight agent proof steps of the node
(blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
def Comparisons.Laws (e : Comparisons d)
    (k : ∀ i : Index, Comparison (d.ringed i)) : Prop :=
  TensorLaws d.R e.sigmaR ∧ TensorLaws d.S e.sigmaS ∧
  TensorTransitionLaws d.R e.sigmaR ∧ TensorTransitionLaws d.S e.sigmaS ∧
  e.KappaTransitionLaws ∧
  (∀ {i j : Index} (t : i ⟶ j) (P Q : Complex (d.R.obj i)),
    e.kappaC t (total P Q) ≪≫
        (pull (d.ringed j)).mapIso (e.sigmaRC t P Q) ≪≫
        comparison (d.ringed j) (k j)
          ((extend (d.R.map t)).obj P) ((extend (d.R.map t)).obj Q) =
      (extend (d.S.map t)).mapIso (comparison (d.ringed i) (k i) P Q) ≪≫
        e.sigmaSC t ((pull (d.ringed i)).obj P) ((pull (d.ringed i)).obj Q) ≪≫
        (totalIso (e.kappaC t P) (e.kappaC t Q))) ∧
  (∀ (i : Index) (P : Complex (d.R.obj i)),
    e.kappaC (𝟙 i) P ≪≫
        (pull (d.ringed i)).mapIso ((diagramUnit d.R i).app P) =
      (diagramUnit d.S i).app ((pull (d.ringed i)).obj P)) ∧
  (∀ {i j l : Index} (a : i ⟶ j) (b : j ⟶ l) (P : Complex (d.R.obj i)),
    (extend (d.S.map b)).mapIso (e.kappaC a P) ≪≫
        e.kappaC b ((extend (d.R.map a)).obj P) ≪≫
        (pull (d.ringed l)).mapIso ((diagramComp d.R a b).app P) =
      (diagramComp d.S a b).app ((pull (d.ringed i)).obj P) ≪≫ e.kappaC (a ≫ b) P) ∧
  (∀ {i j : Index} (t : i ⟶ j)
      (P Q : Complex (d.R.obj i)) (P' Q' : Complex (d.R.obj j))
      (f : (extend (d.R.map t)).obj P ⟶ P')
      (g : (extend (d.R.map t)).obj Q ⟶ Q'),
    (extend (d.S.map t)).map (comparison (d.ringed i) (k i) P Q).hom ≫
        (e.sigmaSC t ((pull (d.ringed i)).obj P) ((pull (d.ringed i)).obj Q)).hom ≫
        (totalMap (e.pullArrow t P P' f) (e.pullArrow t Q Q' g)) =
      e.pullArrow t (total P Q) (total P' Q') (e.tensorArrow t P Q P' Q' f g) ≫
        (comparison (d.ringed j) (k j) P' Q').hom)

/-- Unique simultaneous normalized comparisons, satisfying the full strict
coefficient calculus on possibly unbounded complexes.
Source: Stacks 03EL, 07A4 and the eight agent calculations recorded in the node
(blueprint: lem-pur-strict-coefficient-comparison-calculus).

Proof:
1. Apply lem-pur-cochain-pullback-tensor-coherence at each vertex and to each
   identity-topos coefficient arrow to obtain c and sigma. Factor the compatible
   coefficient square in its two orders; scalar association gives kappa.
2. Balance the forward kappa formula using i_X phi = phi' i_Y. Balance its inverse
   using the same square. Their composites are identities on generalized local
   tensors. def-pur-sheaf-tensor-product and
   def-weil-presheaf-modules-sheafification extend these identities uniquely.
3. Sigma inserts one in its second factor; its inverse multiplies the two scalars.
   Tensor balancing proves both formulas and their mutual inverseness. The
   universal property gives naturality and uniqueness of both families.
4. The maps preserve degree. Naturality gives commutation with d tensor 1 and
   1 tensor d separately; additivity preserves (-1)^p. The direct-sum universal
   property in def-pc-tensor-complex-sheaves gives the unbounded chain maps.
5. For an arbitrary semilinear transition, both kappa routes give
   rho(b) i(rho(a)) tensor (1 tensor t(x)); the inverse uses the phi square.
   Sigma and c give (rho(b) tensor t(x)) tensor (1 tensor t(y)). These identities
   hold for every arrow, and for arbitrary scalar-extension adjoints f and g.
6. On b tensor (a tensor (x tensor y)) the two coefficient-square routes give
   (b i(a) tensor (1 tensor x)) tensor (1 tensor (1 tensor y)). Sheafification
   and direct-sum uniqueness give the equality of isomorphisms and inverses.
7. Scalar units multiply a tensor x to ax. Both kappa and sigma then become
   identities. Scalar associators multiply d tensor (b tensor x) to d i(b)
   tensor x; their inverses insert one. These are the adjoint-uniqueness maps
   used in scalarUnit and scalarComp.
8. The two successive kappa routes multiply to d i12(b) i02(a); successive sigma
   routes give (d i12(b) tensor x) tensor (1 tensor y). Balancing, sheafification
   and the direct-sum universal property give every composition equation.
   Equality of isomorphisms gives the inverse equations. No flatness, nonzero
   ring, boundedness or normalization of the sequence transitions was used.
-/
theorem strictCoefficientComparisonCalculus (d : Diagram (J := J) (K := K))
    (k : ∀ i : Index, Comparison (d.ringed i)) :
    ∃! e : Comparisons d, e.Normalized k ∧ e.Laws k := by
  sorry

end CategoryTheory.CochainPullback.StrictCoefficient
