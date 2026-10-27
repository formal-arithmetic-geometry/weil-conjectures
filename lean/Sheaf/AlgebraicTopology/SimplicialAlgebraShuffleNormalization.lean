module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Sheaf.CategoryTheory.DgAlgebraDerivedCategory
public import Sheaf.AlgebraicTopology.SimplexLatticeShuffleBoundary
import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
import Mathlib.Algebra.Homology.Homotopy

/-! # Shuffle normalization of simplicial commutative algebras

Source: Stacks Project, simplicial.tex, Tags 017V, 019A, 019C and
remark-degenerate-subcomplex, for the additive quotient normalization. The shuffle
calculation is the agent-written prerequisite to the current blueprint's direct-images
proof (3); Weibel, Section 8.5, is listed as WANTED in the DAG source
(blueprint: lem-sfb-simplicial-algebra-shuffle-normalization).

The target consists of commutative monoids in integer cochain complexes of modules
over `ULift.{v} D`, with carriers lifted to `max u v`. Restricting scalars along
`ULift.ringEquiv.symm` recovers D-modules. No ring/algebra universe equality is imposed.
This is the D-linear version of `CategoryTheory.DgAlgebra.Algebra`: its monoid laws
are associativity and unity, its chain-map law is Leibniz, and its Koszul braiding
expresses graded commutativity. The theorem specifies the quotient, product and maps;
it does not choose unspecified dg-algebra replacements.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Simplicial Opposite
open scoped TensorProduct BigOperators

namespace AlgebraicTopology.SimplicialAlgebraShuffleNormalization

variable (D : Type u) [CommRing D]

/-- Forget multiplication and canonically lift scalars and carriers to a common universe.
The scalar action is `(ULift.up d) • (ULift.up x) = ULift.up (d • x)`.
This preserves independent universes for D and the simplicial algebra.
Source: simplicial.tex, additive normalization
(blueprint: lem-sfb-simplicial-algebra-shuffle-normalization). -/
def modules : CommAlgCat.{v} D ⥤ ModuleCat.{max u v} (ULift.{v} D) where
  obj E := ModuleCat.of (ULift.{v} D) (ULift.{u} E)
  map f := ModuleCat.ofHom
    { toFun := fun x ↦ ULift.up (f.hom x.down)
      map_add' := fun x y ↦ congrArg ULift.up (map_add f.hom x.down y.down)
      map_smul' := fun r x ↦ congrArg ULift.up (f.hom.toLinearMap.map_smul r.down x.down) }

/-- The alternating-face complex, reindexed n ↦ -n and extended by zero.
Source: simplicial.tex, Tag 019A
(blueprint: lem-sfb-simplicial-algebra-shuffle-normalization). -/
def chains : SimplicialObject (CommAlgCat.{v} D) ⥤
    CochainComplex (ModuleCat.{max u v} (ULift.{v} D)) ℤ :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ (CommAlgCat D) (ModuleCat.{max u v} (ULift.{v} D))).obj
      (modules D) ⋙ alternatingFaceMapComplex (ModuleCat.{max u v} (ULift.{v} D)) ⋙
    ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{max u v} (ULift.{v} D))

/-- The canonical identification C(P)^(-n) = P_n.
Source: simplicial.tex, Tag 019A
(blueprint: lem-sfb-simplicial-algebra-shuffle-normalization). -/
def chainsTerm (P : SimplicialObject (CommAlgCat.{v} D)) (n : ℕ) :
    ((chains D).obj P).X (-(n : ℤ)) ≅ (modules D).obj (P.obj (op ⦋n⦌)) :=
  (AlternatingFaceMapComplex.obj (P ⋙ modules D)).extendXIso
    ComplexShape.embeddingDownNat rfl

/-- The sum of the images of all degeneracies into P_n; its degree-zero value is zero.
Source: simplicial.tex, remark-degenerate-subcomplex
(blueprint: lem-sfb-simplicial-algebra-shuffle-normalization). -/
def degenerates (P : SimplicialObject (CommAlgCat.{v} D)) :
    (n : ℕ) → Submodule D (P.obj (op ⦋n⦌))
  | 0 => ⊥
  | n + 1 => ⨆ i : Fin (n + 1), LinearMap.range (P.σ i).hom.toLinearMap

/-- The quotient module P_n/J_n, without treating J_n as an ordinary ideal.
Source: simplicial.tex, remark-degenerate-subcomplex
(blueprint: lem-sfb-simplicial-algebra-shuffle-normalization). -/
abbrev quotient (P : SimplicialObject (CommAlgCat.{v} D)) (n : ℕ) :=
  (P.obj (op ⦋n⦌)) ⧸ degenerates D P n

/-- Evaluation of the signed shuffle sum on representatives. The path coordinates
are the two prefix-count surjections, equivalently the displayed degeneracy strings.
The reused `pathSign` counts vertical-before-horizontal inversions, the sign of μ then ν.
Source: the node's displayed shuffle formula, direct-images proof (3)
(blueprint: lem-sfb-simplicial-algebra-shuffle-normalization). -/
def shuffle (P : SimplicialObject (CommAlgCat.{v} D)) (p q : ℕ)
    (x : P.obj (op ⦋p⦌)) (y : P.obj (op ⦋q⦌)) : P.obj (op ⦋p + q⦌) :=
  letI : Fintype (SimplexLatticeShuffle.LatticePath p q) := Fintype.ofFinite
    {w : Fin (p + q + 1) → Fin (p + 1) × Fin (q + 1) //
      Monotone w ∧ ∀ k, (w k).1.val + (w k).2.val = k.val}
  ∑ w : SimplexLatticeShuffle.LatticePath p q,
    SimplexLatticeShuffle.pathSign w •
      ((P.map (SimplexCategory.mkHom
        { toFun := fun k ↦ (w.val k).1
          monotone' := fun _ _ h ↦ (w.property.1 h).1 }).op).hom x *
       (P.map (SimplexCategory.mkHom
        { toFun := fun k ↦ (w.val k).2
          monotone' := fun _ _ h ↦ (w.property.1 h).2 }).op).hom y)

/-- Homogeneous multiplication in a commutative monoid in cochain complexes.
Source: dga.tex, definition-dga, with D-linear coefficients
(blueprint: lem-sfb-simplicial-algebra-shuffle-normalization). -/
def mul (A : CommMon (CochainComplex (ModuleCat.{max u v} (ULift.{v} D)) ℤ))
    (i j k : ℤ) (h : i + j = k) (x : A.X.X i) (y : A.X.X j) : A.X.X k :=
  ((MonObj.mul (X := A.X)).f k)
    ((HomologicalComplex.ιTensorObj A.X A.X i j k h) (x ⊗ₜ[ULift.{v} D] y))

/-- The degree-zero unit of the dg algebra, evaluated on 1 in D.
Source: dga.tex, definition-dga, with D-linear coefficients
(blueprint: lem-sfb-simplicial-algebra-shuffle-normalization). -/
def unit (A : CommMon (CochainComplex (ModuleCat.{max u v} (ULift.{v} D)) ℤ)) : A.X.X 0 :=
  ((MonObj.one (X := A.X)).f 0)
    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (ModuleCat.of (ULift.{v} D) (ULift.{v} D))).inv 1)

/-- The constant simplicial commutative D-algebra.
Source: simplicial.tex, constant simplicial objects
(blueprint: lem-sfb-simplicial-algebra-shuffle-normalization). -/
abbrev constant (E : CommAlgCat.{v} D) : SimplicialObject (CommAlgCat.{v} D) :=
  (Functor.const SimplexCategoryᵒᵖ).obj E

/-- The ordinary D-algebra E in cochain degree zero, on underlying modules.
Source: the constant and augmentation clauses of the node
(blueprint: lem-sfb-simplicial-algebra-shuffle-normalization). -/
def degreeZero (E : CommAlgCat.{v} D) : CochainComplex (ModuleCat.{max u v} (ULift.{v} D)) ℤ :=
  (HomologicalComplex.single (ModuleCat.{max u v} (ULift.{v} D))
    (ComplexShape.up ℤ) 0).obj ((modules D).obj E)

/-- The canonical degree-zero identification E[0]^0 = E.
Source: the constant and augmentation clauses of the node
(blueprint: lem-sfb-simplicial-algebra-shuffle-normalization). -/
def degreeZeroTerm (E : CommAlgCat.{v} D) : (degreeZero D E).X 0 ≅ (modules D).obj E :=
  HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((modules D).obj E)

/-- Quotient normalization has precisely the shuffle dg-algebra structure, is natural,
is a quasi-isomorphic quotient with split terms, preserves degreewise flatness, and
identifies constants and their induced augmentations with the ordinary algebra in degree zero.
The maps `a` are the canonical unnormalized augmentations on constant objects. Their
component at zero and their target supported at zero uniquely determine them. Likewise
`c` is uniquely determined by its component at zero. The product formula on constants
is ordinary multiplication, so these constant identifications are dg-algebra identifications.

Source: simplicial.tex, Tags 017V, 019A, 019C and remark-degenerate-subcomplex;
agent-written shuffle calculation for current blueprint direct-images proof (3)
(blueprint: lem-sfb-simplicial-algebra-shuffle-normalization).

Proof, in the order of the DAG's thirteen steps:
1. Simplicial identities cancel pairs in the alternating differential squared. On a
   degeneracy, the two identity faces cancel, and all other faces remain degenerate.
   Thus J is a natural subcomplex and the quotient map is a chain map.
2. Let K_n be the intersection of positive-face kernels. Apply E_j=1-s_(j-1)d_j in
   descending j. The resulting rho maps into K, fixes K, and differs from 1 by J.
3. Commute s_i through the factors E_j with j>i+1. The next factor E_(i+1) kills s_i.
   Hence rho kills J and P_n=K_n direct-sum J_n, also in degree zero.
4. On K the differential is d_0. The induced K→P/J is a complex isomorphism, with
   inverse [z]↦rho(z). Its inclusion into P gives the natural degreewise sections.
5. Use lem-cbc-normalized-alternating-homotopy-equivalence for the inclusion K→C.
   Reindex and extend by zero; lem-weil-pbc-homotopic-maps-equal-cohomology makes it
   a quasi-isomorphism. Since K→N is an isomorphism, q is a quasi-isomorphism.
6. The path coordinates are the prefix-count surjections for μ and ν, so evaluating
   their simplicial operators gives exactly the degeneracy-string sum in the node.
7. Evaluate lem-sfb-simplex-lattice-shuffle-boundary on x and y. Ring-map faces commute
   with evaluation. Its boundary identity gives Leibniz, omitting zero-degree terms.
8. If an input is degenerate, both coordinate operators repeat at the edge crossing
   that input's repeated position. Each summand is therefore a common degeneracy of
   a product. Bilinearity descends the product and Leibniz to the quotient.
9. Both bracketings of three products index words in three letters. Flattening nested
   shuffles preserves terms and signs, proving associativity even for empty blocks.
10. Interchanging blocks changes the sign by (-1)^(pq); levelwise commutativity gives
    graded commutativity. The unique (0,q) shuffle gives unit [1] and the D-action.
11. Simplicial algebra maps preserve the sum termwise, as well as its unit. Quotient
    maps respect identities and compositions, giving the dg-algebra-valued functor.
12. Apply lem-weil-pbc-flat-module-retract to the quotient and the section in step 4.
    The zero terms in positive cochain degrees are also flat.
13. For a constant E all positive-degree degeneracies are identities, so J_n=E for
    n>0 and J_0=0. The (0,0) product is ordinary multiplication. The augmentation
    factors through q. Its induced map is a quasi-isomorphism by two-out-of-three.
    Taking E=D gives the final canonical constant identification. -/
theorem exists_shuffle_normalization :
    ∃ (N : SimplicialObject (CommAlgCat.{v} D) ⥤
        CommMon (CochainComplex (ModuleCat.{max u v} (ULift.{v} D)) ℤ))
      (q : chains D ⟶ N ⋙ CommMon.forget _)
      (e : ∀ (P : SimplicialObject (CommAlgCat.{v} D)) (n : ℕ),
        (N.obj P).X.X (-(n : ℤ)) ≅ ModuleCat.of (ULift.{v} D) (ULift.{u} (quotient D P n)))
      (c : ∀ E : CommAlgCat.{v} D, (N.obj (constant D E)).X ≅ degreeZero D E)
      (a : ∀ E : CommAlgCat.{v} D, (chains D).obj (constant D E) ⟶ degreeZero D E),
      (∀ (P : SimplicialObject (CommAlgCat.{v} D)) (n : ℕ),
        (q.app P).f (-(n : ℤ)) ≫ (e P n).hom =
          (chainsTerm D P n).hom ≫ ModuleCat.ofHom
            { toFun := fun x ↦ ULift.up ((degenerates D P n).mkQ x.down)
              map_add' := fun x y ↦ congrArg ULift.up (map_add _ x.down y.down)
              map_smul' := fun r x ↦ congrArg ULift.up (map_smul _ r.down x.down) }) ∧
      (∀ P : SimplicialObject (CommAlgCat.{v} D), QuasiIso (q.app P)) ∧
      (∀ (P : SimplicialObject (CommAlgCat.{v} D)) (i : ℤ),
        0 < i → IsZero ((N.obj P).X.X i)) ∧
      (∀ (P : SimplicialObject (CommAlgCat.{v} D)) (p q' : ℕ)
          (x : P.obj (op ⦋p⦌)) (y : P.obj (op ⦋q'⦌)),
        mul D (N.obj P) (-(p : ℤ)) (-(q' : ℤ)) (-(p + q' : ℕ) : ℤ) (by omega)
          ((e P p).inv (ULift.up (Submodule.Quotient.mk x)))
          ((e P q').inv (ULift.up (Submodule.Quotient.mk y))) =
        (e P (p + q')).inv (ULift.up (Submodule.Quotient.mk (shuffle D P p q' x y)))) ∧
      (∀ P : SimplicialObject (CommAlgCat.{v} D),
        unit D (N.obj P) = (e P 0).inv (ULift.up (Submodule.Quotient.mk (1 : P.obj (op ⦋0⦌))))) ∧
      (∀ (P : SimplicialObject (CommAlgCat.{v} D)) (n : ℕ),
        ∃ s : quotient D P n →ₗ[D] P.obj (op ⦋n⦌),
          (degenerates D P n).mkQ.comp s = LinearMap.id) ∧
      (∀ P : SimplicialObject (CommAlgCat.{v} D),
        (∀ n : ℕ, Module.Flat D (P.obj (op ⦋n⦌))) →
          ∀ i : ℤ, Module.Flat D
            ((ModuleCat.restrictScalars (ULift.ringEquiv.symm : D ≃+* ULift.{v} D).toRingHom).obj
              ((N.obj P).X.X i))) ∧
      (∀ (E : CommAlgCat.{v} D) (x : E),
        (degreeZeroTerm D E).hom ((c E).hom.f 0
          ((e (constant D E) 0).inv (ULift.up (Submodule.Quotient.mk x)))) = ULift.up x) ∧
      (∀ E : CommAlgCat.{v} D,
        (a E).f 0 ≫ (degreeZeroTerm D E).hom = (chainsTerm D (constant D E) 0).hom) ∧
      (∀ E : CommAlgCat.{v} D, q.app (constant D E) ≫ (c E).hom = a E) ∧
      (∀ (P : SimplicialObject (CommAlgCat.{v} D)) (E : CommAlgCat.{v} D)
          (ε : P ⟶ constant D E),
        q.app P ≫ (CommMon.forget _).map (N.map ε) ≫ (c E).hom =
          (chains D).map ε ≫ a E) ∧
      (∀ (P : SimplicialObject (CommAlgCat.{v} D)) (E : CommAlgCat.{v} D)
          (ε : P ⟶ constant D E),
        QuasiIso ((chains D).map ε ≫ a E) →
          QuasiIso ((CommMon.forget _).map (N.map ε) ≫ (c E).hom)) := by
  sorry

end AlgebraicTopology.SimplicialAlgebraShuffleNormalization
