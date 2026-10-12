## What changed

Marked `CategoryTheory.injective_presheaf_module_cech_cocycle_lift` as
`STATEMENT-DISPUTED`, without changing its signature or proof. Removed the unused `Sheaf.Paper.PowerSetComplexContractible` public import; the file still compiles.
The theorem is false with its independent universe parameters. The comment and
this report are the delivery; the scratch experiments are not library modules.

## Proved and sorry left

The item's sole sorry remains:
`CategoryTheory.injective_presheaf_module_cech_cocycle_lift`
(node `lem-weil-pbc-injective-presheaf-module-cech-cocycle-lift`).
No new library theorem or sorry is added. This is a disputed-statement delivery,
not a claimed proof or a reduction to an unproved equivalent statement.

The counterexample's size-collapse and injectivity arguments were checked by
`lcompile.py` in `scratchpad/Collapse.lean`, reproduced below. This scratch file
compiles without errors, warnings, or sorry. The construction of the chosen
fibre products and the complete cocycle verification below are mathematical
arguments, not claimed to have been fully formalized in that scratch file.

## No longer needed

Removed public import `Sheaf.Paper.PowerSetComplexContractible`; no node or module is pruned because the disputed theorem remains the item's only declaration.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: injectivity in `PresheafOfModules.{s} R` only gives extensions
along monomorphisms between s-small-valued module presheaves. The ring universe
r, hom universe v, and indexing universe w in this theorem are unrelated to s.
The free representables and their coproducts in steps 1--4 of the node can lie
outside this category. `PresheafOfModules.freeYonedaEquiv` in Mathlib explicitly
uses the same universe for the homs, rings, and module values. Its signature does
not justify those steps with the parameters of this theorem.

Here is a concrete counterexample, taking s = r = 0 and C = Type 1 (the category
of types in universe 1), so u = 2 and v = 1. Let R be the constant presheaf Z.
For an injective small abelian group A, define M_A(X) = A when X is nonempty and
M_A(X) = 0 when X is empty. Its restrictions between nonempty objects are the
identity; a restriction to an empty object is zero. The underlying abelian
presheaf is called `positiveConst A` in the scratch verification below.

First, EVERY universe-0-valued abelian presheaf F on Type 1 sends parallel maps
f,g : X -> Y to equal homomorphisms. Suppose not. Set P = (Type 0 -> Y), an
object of Type 1. For each z : Type 0 let ev_z : P -> Y be evaluation at z.
If F(ev_z) = F(ev_z') for z != z', precompose the evaluations with the function
k : X -> P that assigns f(x) at z and g(x) elsewhere. Contravariance then
implies F(f) = F(g), a contradiction. Thus z -> F(ev_z) injects Type 0 into
the SMALL hom type Hom(F(Y),F(P)). This contradicts Mathlib `not_small_type`.
The scratch theorem `large_type_presheaf_map_eq` proves exactly this argument.

Second, M_A is injective among small-valued abelian presheaves. Given a mono
m : F -> G and a : F -> M_A, extend the component a_1 : F(1) -> A along the
mono m_1 : F(1) -> G(1), obtaining b_1 by injectivity of A. For each nonempty X,
choose p_X : 1 -> X and put b_X = b_1 o G(p_X); for empty X use zero.
The collapse of parallel maps makes this natural: for f : Y -> X, the two
maps 1 -> X, namely f o p_Y and p_X, induce the same G-restriction.
Naturality of m and a and m_1 followed by b_1 = a_1 prove m followed by b = a
at each nonempty X. At empty X both sides have zero target. This is compiled
as `positiveConst_injective`. Making this a presheaf of Z-modules preserves
injectivity: forget a module mono, apply the preceding injectivity, and observe
that all additive component maps are Z-linear. This is compiled as
`positiveConstModule_injective`, and its specialization to A = Q also compiles.

Third, take U = {0,1,2}, embedded into Type 1 by ULift. The index type T is
Fin 3. Use the three two-element subsets E_0={0,1}, E_1={1,2}, E_2={2,0}, with
their inclusion maps into U. Choose their ordinary iterated fibre products,
with the degree-zero objects exactly E_i. Such choices give a SiteCechComplex:
in degree p the product represents elements x of U belonging to every
E_(t(k)); projections and index maps are the coordinate-forgetting maps.
The universal property is the usual fibre-product universal property of sets.
Repeated indices give E_i or a pairwise intersection; the product is empty
precisely when the tuple contains all three distinct indices. In particular
all pairwise intersections are nonempty, but the triple intersection is empty.

Take M = M_Q. Every nonempty product has sections Q, all restrictions between
nonempty products are the identity, and empty products have sections zero.
Define the degree-one cochain c by c(0,1)=1, c(1,0)=-1 and c(i,j)=0 for all
other ordered pairs (including repetitions). It is a cocycle. On a triple
with three distinct indices the target group is zero. On a triple with
repetitions the alternating sum c(j,k)-c(i,k)+c(i,j) is zero: if i=j or j=k
the two equal terms cancel and the diagonal term is zero; if i=k the two
oppositely oriented terms cancel. These cover every triple not containing all
three distinct indices, hence differentialValue in degree one is zero.

There is no degree-zero primitive b. The three ordered pairs (0,1), (1,2),
and (2,0) would require respectively
b(1)-b(0)=1, b(2)-b(1)=0, and b(0)-b(2)=0.
Adding them gives 0=1 in Q. The final scratch example checks this contradiction
with `linarith`. Therefore the conclusion of the item fails for q=0 despite
its injectivity hypothesis. No change to a target or a weaker substitute has
been made. The second reader should confirm this counterexample and route the
necessary universe/interface repair to the maintainer.

Searches: LeanFinder for positive Cech cocycles of injective module presheaves;
Loogle for `ShortComplex.Exact.descToInjective`; launcher grep for
`not_small_type|PresheafOfModules.freeYonedaEquiv|comp_descToInjective`;
and local rg in Mathlib's Presheaf/Generator, Presheaf/Free, Presheaf/EpiMono,
ModuleCat/Ulift and the project's Cech modules. The source-library theorem
`Presheaf.exactAt_cechComplex_of_injective` requires module values in the hom
and indexing universe and does not repair the mismatch. The source text cited
by the DAG is not available in this clone's literature directory; the
counterexample and the scratch verification do not require that text.

The following is the complete compiled scratch verification (not a new module
of the delivery and not a modification of a public library interface):

```lean
module
public import Mathlib.Algebra.Category.Grp.Injective
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Logic.Small.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Data.Rat.Defs
@[expose] public section
universe s
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
theorem large_type_presheaf_map_eq
    (F : (Type (s + 1))ᵒᵖ ⥤ AddCommGrpCat.{s})
    {X Y : Type (s + 1)} (f g : X ⟶ Y) : F.map f.op = F.map g.op := by
  classical
  by_contra hfg
  let P : Type (s + 1) := Type s → Y
  let ev (z : Type s) : P ⟶ Y := ↾fun p ↦ p z
  have hi : Function.Injective (fun z : Type s ↦ F.map (ev z).op) := by
    intro z z' h
    by_contra hzz
    let k : X ⟶ P := ↾fun x a ↦ if a = z then f x else g x
    have hk : k ≫ ev z = f := by ext x; simp [k, ev]
    have hk' : k ≫ ev z' = g := by ext x; simp [k, ev, Ne.symm hzz]
    apply hfg
    have hh := congrArg (fun a ↦ a ≫ F.map k.op) h
    simpa only [← F.map_comp, ← op_comp, hk, hk'] using hh
  exact not_small_type.{s, s} (small_of_injective hi)

private noncomputable def positiveConstObj (A : AddCommGrpCat.{s}) (X : Type (s + 1)) :
    AddCommGrpCat.{s} := by
  classical
  exact if Nonempty X then A else 0

private noncomputable def positiveConstMap (A : AddCommGrpCat.{s})
    {X Y : Type (s + 1)} (f : X ⟶ Y) : positiveConstObj A Y ⟶ positiveConstObj A X := by
  classical
  by_cases hx : Nonempty X
  · have hy : Nonempty Y := hx.map f
    exact eqToHom (show positiveConstObj A Y = A by simp [positiveConstObj, hy]) ≫
      eqToHom (show A = positiveConstObj A X by simp [positiveConstObj, hx])
  · exact 0

private noncomputable def positiveConst (A : AddCommGrpCat.{s}) :
    (Type (s + 1))ᵒᵖ ⥤ AddCommGrpCat.{s} where
  obj X := positiveConstObj A X.unop
  map f := positiveConstMap A f.unop
  map_id X := by
    classical
    by_cases hx : Nonempty X.unop
    · simp [positiveConstMap, hx]
    · have hi : IsZero (positiveConstObj A X.unop) := by
        simpa [positiveConstObj, hx] using (isZero_zero AddCommGrpCat.{s})
      exact hi.eq_of_tgt _ _
  map_comp {X Y Z} f g := by
    classical
    by_cases hz : Nonempty Z.unop
    · have hy := hz.map g.unop
      have hx := hy.map f.unop
      simp [positiveConstMap, hy, hz]
    · have : IsZero (positiveConstObj A Z.unop) := by
        simpa [positiveConstObj, hz] using (Limits.isZero_zero AddCommGrpCat.{s})
      exact this.eq_of_tgt _ _

private abbrev OneLarge : Type (s + 1) := ULift.{s + 1, 0} PUnit

private noncomputable def positiveConstLift (A : AddCommGrpCat.{s})
    (G : (Type (s + 1))ᵒᵖ ⥤ AddCommGrpCat.{s}) (b : G.obj (op OneLarge) ⟶ A) :
    G ⟶ positiveConst A where
  app X := by
    classical
    exact if hx : Nonempty X.unop then
      G.map (↾fun _ : OneLarge ↦ Classical.choice hx).op ≫ b ≫
        eqToHom (show A = positiveConstObj A X.unop by simp [positiveConstObj, hx])
    else 0
  naturality {X Y} f := by
    classical
    by_cases hy : Nonempty Y.unop
    · have hx := hy.map f.unop
      simp only [dif_pos hy, dif_pos hx, positiveConst, positiveConstMap]
      simp only [Category.assoc, eqToHom_trans]
      rw [← Category.assoc, ← G.map_comp]
      have he := large_type_presheaf_map_eq G
        ((↾fun _ : OneLarge ↦ Classical.choice hy) ≫ f.unop)
        (↾fun _ : OneLarge ↦ Classical.choice hx)
      simpa only [op_comp, Quiver.Hom.op_unop] using congrArg (fun a ↦ a ≫ b ≫
        eqToHom (show A = positiveConstObj A Y.unop by simp [positiveConstObj, hy])) he
    · have hi : IsZero ((positiveConst A).obj Y) := by
        simpa [positiveConst, positiveConstObj, hy] using (isZero_zero AddCommGrpCat.{s})
      exact hi.eq_of_tgt _ _

private theorem positiveConst_injective (A : AddCommGrpCat.{s}) [Injective A] :
    Injective (positiveConst A) := by
  classical
  constructor
  intro F G a m hm
  let : Mono m := hm
  have : Mono (m.app (op OneLarge)) := inferInstance
  let e : (positiveConst A).obj (op OneLarge) ≅ A :=
    eqToIso (by simp [positiveConst, positiveConstObj, OneLarge])
  let b : G.obj (op OneLarge) ⟶ A := Injective.factorThru (a.app _ ≫ e.hom) (m.app _)
  refine ⟨positiveConstLift A G b, ?_⟩
  apply NatTrans.ext
  funext X
  by_cases hx : Nonempty X.unop
  · let p : OneLarge ⟶ X.unop := ↾fun _ ↦ Classical.choice hx
    change m.app X ≫ ((positiveConstLift A G b).app X) = a.app X
    simp only [positiveConstLift, dif_pos hx]
    change m.app X ≫ (G.map p.op ≫ b ≫ _) = a.app X
    rw [← Category.assoc, ← m.naturality p.op, Category.assoc]
    rw [← Category.assoc (m.app _) b]
    dsimp [b]
    rw [Injective.comp_factorThru]
    rw [Category.assoc, ← Category.assoc (F.map p.op) (a.app _), a.naturality p.op]
    simp [e, positiveConst, positiveConstMap, OneLarge,
      dif_pos (show Nonempty PUnit.{1} from ⟨PUnit.unit⟩)]
  · have hi : IsZero ((positiveConst A).obj X) := by
      simpa [positiveConst, positiveConstObj, hx] using (isZero_zero AddCommGrpCat.{s})
    exact hi.eq_of_tgt _ _

private abbrev intRings : (Type (s + 1))ᵒᵖ ⥤ RingCat :=
  (Functor.const _).obj (RingCat.of ℤ)

private noncomputable def positiveConstModule (A : AddCommGrpCat.{s}) :
    PresheafOfModules.{s} intRings.{s} := by
  letI (X : (Type (s + 1))ᵒᵖ) : Module (intRings.obj X) ((positiveConst A).obj X) :=
    (inferInstance : Module ℤ ((positiveConst A).obj X))
  exact PresheafOfModules.ofPresheaf (positiveConst A) (by
    intro X Y f r m
    exact map_zsmul ((positiveConst A).map f).hom r m)

set_option backward.isDefEq.respectTransparency false in
private theorem positiveConstModule_injective (A : AddCommGrpCat.{s}) [Injective A] :
    Injective (positiveConstModule A) := by
  classical
  have : Injective (positiveConst A) := positiveConst_injective A
  constructor
  intro F G a m hm
  let : Mono m := hm
  let af := (PresheafOfModules.toPresheaf _).map a
  let mf := (PresheafOfModules.toPresheaf _).map m
  have : Mono mf := inferInstance
  have : Injective ((PresheafOfModules.toPresheaf _).obj (positiveConstModule A)) := by
    change Injective (positiveConst A)
    exact positiveConst_injective A
  obtain ⟨b, hb⟩ := Injective.factors af mf
  let bm : G ⟶ positiveConstModule A := PresheafOfModules.homMk b (by
    intro X r x
    change ℤ at r
    convert! map_zsmul (b.app X).hom r x using 1
    · congr 1
      exact @int_smul_eq_zsmul (G.obj X) _ (G.obj X).isModule r x)
  refine ⟨bm, ?_⟩
  apply (PresheafOfModules.toPresheaf _).map_injective
  exact hb

example : Injective (positiveConstModule (AddCommGrpCat.of ℚ)) := by
  apply positiveConstModule_injective

example : ¬ ∃ b : Fin 3 → ℚ,
    b 1 - b 0 = 1 ∧ b 2 - b 1 = 0 ∧ b 0 - b 2 = 0 := by
  rintro ⟨b, h01, h12, h20⟩
  linarith
```

## Second reading by C1

1. **Statements and accidental changes.** Compared the delivered module with the repository version. The theorem signature and all existing declarations are unchanged. The only code edit is removal of an unused public import. Verdict: pass.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it succeeds. The sole `sorry` is the named theorem listed above, and there are no axioms, unsafe declarations, or hollow definitions. Since the theorem is disputed, no proof claim is made. Verdict: pass for the disputed-statement delivery.

3. **Split-off statements.** No theorem was split off and no new node was added. The counterexample is documented in the report and its scratch verification compiles; the original statement is marked `STATEMENT-DISPUTED` rather than weakened. Verdict: pass.

4. **Pruning and route.** The removed import was not used by any declaration in the module. The DAG proof dependencies and unit route are otherwise untouched. Verdict: pass.

5. **DAG agreement.** The existing node's Lean module, declaration, statement, and proof status still match the file. No new node or proof dependency was introduced. Verdict: pass.

Changed only the disputed-status comments, the unused import, and this report; no mathematical statement was altered.
