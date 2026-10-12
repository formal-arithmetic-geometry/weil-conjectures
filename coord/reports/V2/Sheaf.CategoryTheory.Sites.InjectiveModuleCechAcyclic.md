## What changed

Repaired reviewer X-38a84 point 4. In
Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic, replaced RingCat.{r},
AddCommGrpCat.{s}, SheafOfModules.{s}, and T : Type w by their common-universe-v
versions. Updated the docstring and historical dispute comment: the old signature
is refuted, while the corrected statement is now proved from existing declarations.
No Challenge target, existing public definition, or caller signature changes.

The proof transfers injectivity from sheaves to module presheaves, applies the
corrected existing common-universe cocycle-lifting theorem, and proves exactness
and zero homology via Mathlib's abelian-group exactness criterion. Its three
proof-only imports are needed, so the earlier claimed pruning is withdrawn.

Five etale callers cannot apply that restricted theorem since their hom universe
is u and their coefficient/index universe is u+1. Adapted only the invocation
blocks and proof-only imports, preserving their existing signatures and visibility.
They transfer injectivity, use a new max-universe presheaf cocycle-lifting step,
and combine it with a fully written exactness/homology argument. Updated their
DAG proof metadata. No unit realization is bypassed: sk-prop-cd has no realized
statement or step attached to this item.

Change record: coord/changes/injective-module-cech-universes.md, including verbatim
old/new signatures, all direct users and all transitive importers, and holders.

## Proved and sorry left

Closed the item's original hole after the expressly requested signature repair:
CategoryTheory.injective_module_cech_cohomology_isZero
(node lem-weil-pbc-ringed-site-injective-module-cech-acyclic). Its proof body has
no sorry and compiles from the existing common-universe declarations. This is a
proof of the corrected statement, not a proof of the refuted original signature.

Added one named public hole:
CategoryTheory.injective_presheaf_module_cech_cocycle_lift_max
(node lem-weil-pbc-injective-presheaf-module-cech-cocycle-lift-max), in its own
module Sheaf.CategoryTheory.Sites.InjectivePresheafModuleCechCocycleLiftMax.
It states only the presheaf primitive-construction step: no topology, covering,
sheaf condition or sheafification. Its proof is exactly by sorry, with its source
and complete proof in words in the docstring and node. The coefficient/index
universe is max v w and hence contains the hom universe v. Edge cases include
q=0, empty families and lift sets, zero modules and rings; the old Type-1/small-Q
counterexample is excluded by that explicit maximum.

All five adapted callers retain complete proof bodies and add no local holes.
This repair closes one hole and adds one lower hole needed for forced adaptations;
net holes closed minus added is zero. It is a decomposition in the target closure,
not a claim that the corrected theorem or its downstream consequences are already
free of inherited sorryAx. No axiom, hollow definition or arbitrary witness from
an unproved existence theorem is introduced.

The old certified refutation is retained below, including the exact specialized
negation Triangle.false_signature. Its axioms are only propext, Classical.choice
and Quot.sound; it specializes the old signature to u=2,v=1,w=r=s=0 and does not
import the disputed theorem. The certificate remains a scratch artifact, not a
new library module or node.

## No longer needed

No imports are pruned from the item's original repository version: its three
proof-only imports Mathlib.Algebra.Homology.ShortComplex.Ab,
Sheaf.CategoryTheory.InjectiveModulePresheaf, and
Sheaf.CategoryTheory.Sites.InjectivePresheafModuleCechExact are all used again.
The earlier returned delivery's claim that those dependencies were no longer
needed is withdrawn after the universe repair.

The five forced adaptations remove their proof-only import of
Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic. That common-universe
statement cannot serve the larger-coefficient applications. Their node proof
edges are replaced by presheaf injectivity and max-universe cocycle lifting.
The main module remains reached via other imports; no global module pruning is
claimed. The removed proof-dependency node in each of the five adapted callers is
`lem-weil-pbc-ringed-site-injective-module-cech-acyclic`; there are no removed
proof dependencies in the main item. The source's free-complex and Yoneda argument stays below the existing
cocycle-lifting dependency and the new max-universe step.

## Where the brief, the DAG or earlier work was wrong

The previous delivery correctly certified that the independent-universe theorem
was false, but left that false statement as a remaining sorry. Reviewer X-38a84
point 4 requires correcting its interface rather than just reporting the dispute.
The correction requested by the reviewer makes its existing presheaf proof valid.
It also forces five etale applications to change: their coefficient and cover
universes are strictly larger than the hom universe. Preserving those signatures
requires a presheaf lifting step that permits a larger coefficient universe.

Historical STATEMENT-DISPUTED (old signature only): the independent coefficient
universe permits the certified Type-1 triangle counterexample. The new library
statement is not marked disputed. Both its exact requested restrictions and its
actual proof status are recorded in the node; every citing node is accounted for.

Here is the counterexample in words, matching the code below.

1. Work on the category `Type 1`, with small coefficients in `Type 0`.
Every functor from its opposite to a category with small homs sends parallel
maps to the same morphism. If two maps were distinguished, evaluations from
`Type 0 -> Y` would inject `Type 0` into a small hom type, contradicting
`not_small_type`. This is `large_type_functor_map_eq`.

2. A covering presieve is required to be nonempty and jointly surjective on
ordered pairs of points: each pair has lifts into one member of the family.
This precoverage has isomorphisms, is stable under composition and base change,
and has pullbacks. Nonemptiness also applies when the target is empty, so the
empty family does NOT cover the empty object. All these properties are certified.

3. Every small set-valued presheaf is a sheaf for this topology. On a nonempty
object, restriction to a chosen point is invertible by parallel-map collapse.
In a compatible covering family, pair-lifting compares the values at any two
points through a third covering member. They give one common value at the
one-point object, which extends uniquely to the target. Sections over empty
covering members are then forced by compatibility with the chosen nonempty
member. If the target is empty, choose any covering arrow (nonemptiness is
essential); its domain is empty too and it is an isomorphism, giving unique
gluing. `pair_isSheafFor` and `small_type_isSheaf` prove this for the generated
Grothendieck topology. Applying this to the small Hom-valued presheaves proves
`all_isSheaf` for every category with small homs.

4. Hence the inclusion of small abelian sheaves into presheaves is an
equivalence. Its inverse supplies a finite-limit-preserving left adjoint, so
`HasSheafify` holds. Every sheafification unit is invertible and therefore
locally injective and locally surjective. The underlying small set presheaves
are sheaves too, giving `HasSheafCompose (forget AddCommGrpCat)`. Mathlib's
`GrothendieckTopology.WEqualsLocallyBijective.mk'` supplies the second requested
hypothesis. The code constructs both instances without any sorry.

5. The constant integer ring presheaf is a sheaf (including at the empty
object, since only nonempty covers are allowed there). Let the module presheaf
have values Q on nonempty types and zero on empty types, with identity
restrictions between nonempty objects. It is injective: extend an extension
problem at a one-point object using injectivity of Q, then restrict to chosen
points everywhere. Parallel-map collapse supplies naturality. Additive maps
are automatically integer-linear. It is a module sheaf by step 3, and its
presheaf injectivity gives sheaf injectivity since the inclusion preserves
monomorphisms. The ring and module sheaf are `Triangle.rings` and
`Triangle.moduleSheaf`.

6. Cover the three-point type by its three two-point subsets, the edges of a
triangle. Every ordered pair of vertices belongs to an edge, so this is a
covering. Chosen fibre products are the subtypes of vertices belonging to all
the specified edges; their universal properties, projections, degree-zero
identifications and index maps form `Triangle.complex`. Every pairwise product
is nonempty, while the product involving all three distinct edges is empty.

7. Define a degree-one cochain with values 1 on `(0,1)`, -1 on `(1,0)`, and
zero on every other ordered pair. Its differential vanishes: triples with
repetition cancel, and triples with three distinct edges have zero target.
A primitive would imply `b1-b0=1`, `b2-b1=0`, and `b0-b2=0`, impossible over Q.
`c_cocycle` and `c_not_boundary` certify this for the actual restriction
formula. Mathlib's homology/exactness equivalence and `ShortComplex.ab_exact_iff`
then give `cohomology_nonzero`. Applying the proposed universal signature to
this data gives a contradiction; that final exact specialized negation is
`Triangle.false_signature`.

The earlier change record is
`coord/changes/injective-presheaf-module-cech-universes.md`; prior reports are
`coord/reports/C1/Sheaf.CategoryTheory.Sites.InjectivePresheafModuleCechExact.md`
and `coord/reports/E2/Sheaf.CategoryTheory.SiteInjectiveCechAcyclic.md`.
The repaired library statement excludes these universe parameters; the certificate
continues to refute only the old signature. Its existence does not refute the
corrected common-universe theorem. The Type-1 rational example has hom universe 1
and coefficient universe 0, which cannot be expressed as max v w.

Searches performed through the launcher: LeanFinder for positive Cech cohomology
of injective module presheaves; Loogle for injectivity and equivalences; grep for
injectivity and ULift. Local searches covered the source library, Sheaf modules,
Mathlib's module-presheaf/free/ULift/injectivity files, the existing change records,
the node's dependencies and the unit `sk-prop-cd` (which has no realized nodes
at this item). Mathlib's module ULift preservation requires a smallness
hypothesis; it cannot fix the unrestricted statement. The cited Stacks source
file is absent from this machine, but this refutation needs no unavailable text.

The following is the complete scratch certificate. It is embedded so the second
reader and maintainer can reproduce it even though scratch files are not copied
into a delivery. Compile it with the supplied `lcompile.py`; no build or external
search is needed.

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
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Sheaf.CategoryTheory.SiteCechComplex
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.Ab
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

theorem large_type_functor_map_eq
    {D : Type*} [Category.{s} D] (F : (Type (s + 1))ᵒᵖ ⥤ D)
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

noncomputable def positiveConstObj (A : AddCommGrpCat.{s}) (X : Type (s + 1)) :
    AddCommGrpCat.{s} := by
  classical
  exact if Nonempty X then A else 0

noncomputable def positiveConstMap (A : AddCommGrpCat.{s})
    {X Y : Type (s + 1)} (f : X ⟶ Y) : positiveConstObj A Y ⟶ positiveConstObj A X := by
  classical
  by_cases hx : Nonempty X
  · have hy : Nonempty Y := hx.map f
    exact eqToHom (show positiveConstObj A Y = A by simp [positiveConstObj, hy]) ≫
      eqToHom (show A = positiveConstObj A X by simp [positiveConstObj, hx])
  · exact 0

noncomputable def positiveConst (A : AddCommGrpCat.{s}) :
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

abbrev OneLarge : Type (s + 1) := ULift.{s + 1, 0} PUnit

noncomputable def positiveConstLift (A : AddCommGrpCat.{s})
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

theorem positiveConst_injective (A : AddCommGrpCat.{s}) [Injective A] :
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

abbrev intRings : (Type (s + 1))ᵒᵖ ⥤ RingCat :=
  (Functor.const _).obj (RingCat.of ℤ)

noncomputable def positiveConstModule (A : AddCommGrpCat.{s}) :
    PresheafOfModules.{s} intRings.{s} := by
  letI (X : (Type (s + 1))ᵒᵖ) : Module (intRings.obj X) ((positiveConst A).obj X) :=
    (inferInstance : Module ℤ ((positiveConst A).obj X))
  exact PresheafOfModules.ofPresheaf (positiveConst A) (by
    intro X Y f r m
    exact map_zsmul ((positiveConst A).map f).hom r m)

set_option backward.isDefEq.respectTransparency false in
theorem positiveConstModule_injective (A : AddCommGrpCat.{s}) [Injective A] :
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

-- Presheaf injectivity also gives sheaf injectivity when the inclusion preserves monos.
theorem sheaf_module_injective_of_presheaf_injective
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{0})
    [HasSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    (I : SheafOfModules.{0} R) [Injective I.val] : Injective I := by
  constructor
  intro X Y a m hm
  let : Mono m := hm
  have : Mono ((SheafOfModules.forget R).map m) := inferInstance
  have : Injective ((SheafOfModules.forget R).obj I) := ‹Injective I.val›
  obtain ⟨b, hb⟩ := Injective.factors
    ((SheafOfModules.forget R).map a) ((SheafOfModules.forget R).map m)
  refine ⟨(SheafOfModules.forget R).preimage b, ?_⟩
  apply (SheafOfModules.forget R).map_injective
  rw [Functor.map_comp, Functor.map_preimage]
  exact hb

namespace Triangle

abbrev U : Type 1 := ULift.{1} (Fin 3)
abbrev E (i : Fin 3) : Type 1 := ULift.{1} {x : Fin 3 // x ≠ i}
def inclusion (i : Fin 3) : E i ⟶ U := ↾fun x ↦ ⟨x.down.val⟩
abbrev W (p : ℕ) (t : Fin (p + 1) → Fin 3) : Type 1 :=
  ULift.{1} {x : Fin 3 // ∀ k, x ≠ t k}
def pr (p : ℕ) (t : Fin (p + 1) → Fin 3) (k : Fin (p + 1)) : W p t ⟶ E (t k) :=
  ↾fun x ↦ ⟨⟨x.down.val, x.down.property k⟩⟩

theorem zeroPredicate (t : Fin 1 → Fin 3) :
    (fun x : Fin 3 ↦ ∀ k : Fin 1, x ≠ t k) = (fun x ↦ x ≠ t 0) := by
  funext x
  apply propext
  simp

theorem val_cast {P Q : Fin 3 → Prop} (hp : P = Q)
    (h : ULift.{1} {x // P x} = ULift.{1} {x // Q x}) (x : ULift.{1} {x // P x}) :
    ((eqToHom h) x).down.val = x.down.val := by
  subst Q
  cases h
  rfl

def complex : SiteCechComplex E inclusion where
  W := W
  pr := pr
  comm _ _ _ := rfl
  universal p t Z a ha := by
    let b : Z ⟶ W p t := ↾fun z ↦ ⟨⟨(a 0 z).down.val, fun k ↦ by
      have hk := ConcreteCategory.congr_hom (ha k) z
      have hv : (a k z).down.val = (a 0 z).down.val := congrArg ULift.down hk
      exact hv ▸ (a k z).down.property⟩⟩
    refine ⟨b, ?_, ?_⟩
    · intro k
      apply ConcreteCategory.hom_ext
      intro z
      apply ULift.ext
      apply Subtype.ext
      exact (congrArg ULift.down (ConcreteCategory.congr_hom (ha k) z)).symm
    · intro b' hb
      apply ConcreteCategory.hom_ext
      intro z
      apply ULift.ext
      apply Subtype.ext
      exact congrArg (fun x ↦ x.down.val) (ConcreteCategory.congr_hom (hb 0) z)
  W_zero t := by
    change ULift.{1} {x : Fin 3 // ∀ k : Fin 1, x ≠ t k} =
      ULift.{1} {x : Fin 3 // x ≠ t 0}
    congr 2
    funext x
    apply propext
    simp
  pr_zero t := by
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    apply Subtype.ext
    exact (val_cast (zeroPredicate t) _ x).symm
  indexMap t α := ↾fun x ↦ ⟨⟨x.down.val, fun k ↦ x.down.property (α k)⟩⟩
  indexMap_pr _ _ _ := rfl

#check complex
#print axioms large_type_presheaf_map_eq
#print axioms positiveConstModule_injective
#print axioms sheaf_module_injective_of_presheaf_injective
#print axioms complex
end Triangle

namespace Triangle

lemma pairNonempty (t : Fin 2 → Fin 3) : Nonempty (W 1 t) := by
  have hh : ∃ x : Fin 3, x ≠ t 0 ∧ x ≠ t 1 := by
    generalize h0 : t 0 = a
    generalize h1 : t 1 = b
    fin_cases a <;> fin_cases b <;> decide
  obtain ⟨x, h0, h1⟩ := hh
  refine ⟨⟨⟨x, ?_⟩⟩⟩
  intro k
  fin_cases k
  · exact h0
  · exact h1

noncomputable def cv (t : Fin 2 → Fin 3) : ℚ :=
  if t 0 = 0 ∧ t 1 = 1 then 1 else if t 0 = 1 ∧ t 1 = 0 then -1 else 0

noncomputable def c : complex.cochains (positiveConst (AddCommGrpCat.of ℚ)) 1 := by
  classical
  exact fun t ↦ (eqToHom (by
    simp [positiveConst, positiveConstObj, pairNonempty t] :
    AddCommGrpCat.of ℚ = (positiveConst (AddCommGrpCat.of ℚ)).obj (op (W 1 t)))) (cv t)

lemma cv_cocycle (t : Fin 3 → Fin 3) (ht : Nonempty (W 2 t)) :
    cv (t ∘ Fin.succAbove (0 : Fin 3)) - cv (t ∘ Fin.succAbove (1 : Fin 3)) +
      cv (t ∘ Fin.succAbove (2 : Fin 3)) = 0 := by
  obtain ⟨⟨x, hx⟩⟩ := ht
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  generalize ha : t 0 = a at *
  generalize hb : t 1 = b at *
  generalize hc : t 2 = d at *
  fin_cases a <;> fin_cases b <;> fin_cases d <;>
    simp_all [cv, Fin.succAbove] <;> omega

lemma c_cocycle :
    complex.differentialValue (positiveConst (AddCommGrpCat.of ℚ)) 1 c = 0 := by
  classical
  funext t
  change complex.differentialValue (positiveConst (AddCommGrpCat.of ℚ)) 1 c t =
    (0 : (positiveConst (AddCommGrpCat.of ℚ)).obj (op (W 2 t)))
  by_cases ht : Nonempty (W 2 t)
  · have he := cv_cocycle t ht
    let e : (positiveConst (AddCommGrpCat.of ℚ)).obj (op (W 2 t)) ≅
        AddCommGrpCat.of ℚ := eqToIso (by simp [positiveConst, positiveConstObj, ht])
    apply (ConcreteCategory.bijective_of_isIso e.hom).1
    simpa [SiteCechComplex.differentialValue, complex, SiteCechComplex.cochains,
      positiveConst, positiveConstMap, positiveConstObj, ht, c, e,
      pairNonempty, Fin.sum_univ_succ, ← ConcreteCategory.comp_apply,
      eqToHom_trans, sub_eq_add_neg, add_assoc] using he
  · have hz : IsZero ((positiveConst (AddCommGrpCat.of ℚ)).obj (op (W 2 t))) := by
      simpa [positiveConst, positiveConstObj, ht] using (isZero_zero AddCommGrpCat.{0})
    have hz0 := hz.eq_of_tgt (𝟙 _) 0
    simpa using ConcreteCategory.congr_hom hz0
      (complex.differentialValue (positiveConst (AddCommGrpCat.of ℚ)) 1 c t)

#print axioms cv_cocycle
#print axioms c_cocycle
end Triangle

namespace Triangle

lemma vertexNonempty (t : Fin 1 → Fin 3) : Nonempty (W 0 t) := by
  have hh : ∃ x : Fin 3, x ≠ t 0 := by
    generalize h0 : t 0 = a
    fin_cases a <;> decide
  obtain ⟨x, hx⟩ := hh
  refine ⟨⟨⟨x, ?_⟩⟩⟩
  intro k
  fin_cases k
  exact hx

noncomputable def e0 (t : Fin 1 → Fin 3) :
    (positiveConst (AddCommGrpCat.of ℚ)).obj (op (W 0 t)) ≅ AddCommGrpCat.of ℚ := by
  classical
  exact eqToIso (by simp [positiveConst, positiveConstObj, vertexNonempty t])

set_option linter.flexible false in
lemma primitive_relation
    (b : complex.cochains (positiveConst (AddCommGrpCat.of ℚ)) 0)
    (hb : complex.differentialValue (positiveConst (AddCommGrpCat.of ℚ)) 0 b = c)
    (i j : Fin 3) :
    (e0 (fun _ ↦ j)).hom (b (fun _ ↦ j)) -
      (e0 (fun _ ↦ i)).hom (b (fun _ ↦ i)) = cv ![i, j] := by
  classical
  let t : Fin 2 → Fin 3 := ![i, j]
  have h0 : t ∘ Fin.succAbove (0 : Fin 2) = (fun _ : Fin 1 ↦ j) := by
    funext k
    fin_cases k
    rfl
  have h1 : t ∘ Fin.succAbove (1 : Fin 2) = (fun _ : Fin 1 ↦ i) := by
    funext k
    fin_cases k
    rfl
  let e : (positiveConst (AddCommGrpCat.of ℚ)).obj (op (W 1 t)) ≅
      AddCommGrpCat.of ℚ := eqToIso (by simp [positiveConst, positiveConstObj, pairNonempty t])
  have he := congrArg (fun z ↦ e.hom (z t)) hb
  have hn := pairNonempty t
  have hn1 := vertexNonempty (t ∘ Fin.succAbove (1 : Fin 2))
  simp only [SiteCechComplex.differentialValue, Fin.sum_univ_succ] at he
  simp [complex, positiveConst, positiveConstMap, positiveConstObj,
    hn, hn1, e, c, ← ConcreteCategory.comp_apply, eqToHom_trans] at he
  have h0' : t ∘ Fin.succ = (fun _ : Fin 1 ↦ j) := by simpa using h0
  change (e0 (t ∘ Fin.succ)).hom (b (t ∘ Fin.succ)) +
    -(e0 (t ∘ Fin.succAbove (1 : Fin 2))).hom (b (t ∘ Fin.succAbove (1 : Fin 2))) =
      cv t at he
  rw [h0', h1] at he
  simpa only [sub_eq_add_neg, t] using he

lemma c_not_boundary :
    ¬ ∃ b : complex.cochains (positiveConst (AddCommGrpCat.of ℚ)) 0,
      complex.differentialValue (positiveConst (AddCommGrpCat.of ℚ)) 0 b = c := by
  rintro ⟨b, hb⟩
  have h01 := primitive_relation b hb 0 1
  have h12 := primitive_relation b hb 1 2
  have h20 := primitive_relation b hb 2 0
  simp [cv] at h01 h12 h20
  linarith

#print axioms c_not_boundary
end Triangle

namespace Triangle
lemma cohomology_nonzero :
    ¬ IsZero ((complex.cohomologyFunctor 1).obj (positiveConst (AddCommGrpCat.of ℚ))) := by
  intro hz
  have he : (complex.complex (positiveConst (AddCommGrpCat.of ℚ))).ExactAt 1 :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 hz
  rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp),
    ShortComplex.ab_exact_iff] at he
  apply c_not_boundary
  obtain ⟨b, hb⟩ := he c (by
    change (CochainComplex.of.d (complex.cochains (positiveConst (AddCommGrpCat.of ℚ)))
      (complex.differential (positiveConst (AddCommGrpCat.of ℚ))) 1 (1 + 1)) c = 0
    rw [CochainComplex.of_d]
    exact c_cocycle)
  change (CochainComplex.of.d (complex.cochains (positiveConst (AddCommGrpCat.of ℚ)))
    (complex.differential (positiveConst (AddCommGrpCat.of ℚ))) 0 (0 + 1)) b = c at hb
  rw [CochainComplex.of_d] at hb
  exact ⟨b, hb⟩
#print axioms cohomology_nonzero
#print axioms large_type_functor_map_eq
end Triangle

namespace Triangle

def pairCoverage : Precoverage (Type 1) where
  coverings X S := (∃ (Y : Type 1) (f : Y ⟶ X), S f) ∧
    ∀ x y : X, ∃ (Y : Type 1) (f : Y ⟶ X), S f ∧
      ∃ a b : Y, f a = x ∧ f b = y

instance : pairCoverage.HasIsos where
  mem_coverings_of_isIso f := by
    refine ⟨⟨_, f, Presieve.singleton_self f⟩, ?_⟩
    intro x y
    refine ⟨_, f, Presieve.singleton_self f, inv f x, inv f y, ?_, ?_⟩ <;>
      simp [← ConcreteCategory.comp_apply]

lemma covering : Presieve.ofArrows E inclusion ∈ pairCoverage U := by
  refine ⟨⟨_, inclusion 0, Presieve.ofArrows.mk 0⟩, ?_⟩
  intro x y
  have hh : ∃ i : Fin 3, x.down ≠ i ∧ y.down ≠ i := by
    generalize hx : x.down = a
    generalize hy : y.down = b
    fin_cases a <;> fin_cases b <;> decide
  obtain ⟨i, hx, hy⟩ := hh
  refine ⟨_, inclusion i, Presieve.ofArrows.mk i, ⟨⟨x.down, hx⟩⟩, ⟨⟨y.down, hy⟩⟩,
    ?_, ?_⟩ <;> rfl

#print axioms covering
end Triangle

namespace Triangle
instance : pairCoverage.IsStableUnderComposition where
  comp_mem_coverings {ι} {S} {X} f hf {σ} {Y} g hg := by
    constructor
    · obtain ⟨_, _, ⟨i⟩⟩ := hf.1
      obtain ⟨_, _, ⟨j⟩⟩ := (hg i).1
      exact ⟨_, g i j ≫ f i, Presieve.ofArrows.mk (⟨i, j⟩ : Σ i, σ i)⟩
    · intro x y
      obtain ⟨_, _, ⟨i⟩, a, b, ha, hb⟩ := hf.2 x y
      obtain ⟨_, _, ⟨j⟩, c, d, hc, hd⟩ := (hg i).2 a b
      refine ⟨_, g i j ≫ f i, Presieve.ofArrows.mk (⟨i, j⟩ : Σ i, σ i), c, d, ?_, ?_⟩
      · change f i (g i j c) = x
        rw [hc, ha]
      · change f i (g i j d) = y
        rw [hd, hb]

instance : pairCoverage.IsStableUnderBaseChange where
  mem_coverings_of_isPullback {ι} {S} {X} f hf {Y} g {P} p₁ p₂ h := by
    constructor
    · obtain ⟨_, _, ⟨i⟩⟩ := hf.1
      exact ⟨_, p₁ i, Presieve.ofArrows.mk i⟩
    · intro x y
      obtain ⟨_, _, ⟨i⟩, a, b, ha, hb⟩ := hf.2 (g x) (g y)
      let l : OneLarge.{0} ⟶ _ := (h i).lift (↾fun _ ↦ x) (↾fun _ ↦ a)
        (by ext z; exact ha.symm)
      let m : OneLarge.{0} ⟶ _ := (h i).lift (↾fun _ ↦ y) (↾fun _ ↦ b)
        (by ext z; exact hb.symm)
      refine ⟨_, p₁ i, Presieve.ofArrows.mk i, l ⟨PUnit.unit⟩, m ⟨PUnit.unit⟩, ?_, ?_⟩
      · exact ConcreteCategory.congr_hom ((h i).lift_fst (↾fun _ : OneLarge.{0} ↦ x)
          (↾fun _ : OneLarge.{0} ↦ a) (by ext z; exact ha.symm))
          (⟨PUnit.unit⟩ : OneLarge.{0})
      · exact ConcreteCategory.congr_hom ((h i).lift_fst (↾fun _ : OneLarge.{0} ↦ y)
          (↾fun _ : OneLarge.{0} ↦ b) (by ext z; exact hb.symm))
          (⟨PUnit.unit⟩ : OneLarge.{0})

example : pairCoverage.HasPullbacks := inferInstance
end Triangle

namespace Triangle

def point {X : Type 1} (x : X) : OneLarge.{0} ⟶ X := ↾fun _ ↦ x
def toOne (X : Type 1) : X ⟶ OneLarge.{0} := ↾fun _ ↦ ⟨PUnit.unit⟩

lemma map_point_bijective (F : (Type 1)ᵒᵖ ⥤ Type 0) {X : Type 1} (x : X) :
    Function.Bijective (F.map (point x).op) := by
  have hleft : Function.LeftInverse (F.map (toOne X).op) (F.map (point x).op) := by
    intro a
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp,
      large_type_functor_map_eq F (toOne X ≫ point x) (𝟙 X), op_id, F.map_id]
    rfl
  have hright : Function.RightInverse (F.map (toOne X).op) (F.map (point x).op) := by
    intro a
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp,
      large_type_functor_map_eq F (point x ≫ toOne X) (𝟙 _), op_id, F.map_id]
    rfl
  exact ⟨hleft.injective, hright.surjective⟩

lemma compatible_point_eq (F : (Type 1)ᵒᵖ ⥤ Type 0) {X : Type 1} {R : Presieve X}
    (hr : R ∈ pairCoverage X) (t : R.FamilyOfElements F) (ht : t.Compatible)
    {Y Z : Type 1} {f : Y ⟶ X} {g : Z ⟶ X} (hf : R f) (hg : R g) (y : Y) (z : Z) :
    F.map (point y).op (t f hf) = F.map (point z).op (t g hg) := by
  obtain ⟨V, h, hh, a, b, ha, hb⟩ := hr.2 (f y) (g z)
  calc
    _ = F.map (point a).op (t h hh) := ht (point y) (point a) hf hh (by
      ext w
      exact ha.symm)
    _ = F.map (point b).op (t h hh) := by
      rw [large_type_functor_map_eq F (point a) (point b)]
    _ = _ := (ht (point z) (point b) hg hh (by ext w; exact hb.symm)).symm

#print axioms compatible_point_eq
end Triangle

namespace Triangle
lemma pair_isSheafFor (F : (Type 1)ᵒᵖ ⥤ Type 0) {X : Type 1} (R : Presieve X)
    (hr : R ∈ pairCoverage X) : Presieve.IsSheafFor F R := by
  classical
  intro t ht
  by_cases hx : Nonempty X
  · obtain ⟨Y₀, f₀, hf₀, a₀, _, _, _⟩ := hr.2 (Classical.choice hx) (Classical.choice hx)
    let m₀ := F.map (point a₀).op (t f₀ hf₀)
    let s := F.map (toOne X).op m₀
    have hs : t.IsAmalgamation s := by
      intro Y f hf
      by_cases hy : Nonempty Y
      · let y := Classical.choice hy
        apply (map_point_bijective F y).1
        calc
          _ = F.map (point y ≫ f ≫ toOne X).op m₀ := by
            simp [s, op_comp, F.map_comp]
          _ = m₀ := by
            rw [large_type_functor_map_eq F (point y ≫ f ≫ toOne X) (𝟙 _), op_id, F.map_id]
            rfl
          _ = _ := compatible_point_eq F hr t ht hf₀ hf a₀ y
      · let g : Y ⟶ Y₀ := ↾fun y ↦ False.elim (hy ⟨y⟩)
        have hh : g ≫ f₀ = f := by
          apply ConcreteCategory.hom_ext
          intro y
          exact False.elim (hy ⟨y⟩)
        have hc := ht g (𝟙 Y) hf₀ hf (by simpa using hh)
        simp only [op_id, F.map_id, ConcreteCategory.id_apply] at hc
        calc
          _ = F.map (f ≫ toOne X ≫ point a₀).op (t f₀ hf₀) := by
            simp [s, m₀, op_comp, F.map_comp]
          _ = F.map g.op (t f₀ hf₀) := by
            rw [large_type_functor_map_eq F (f ≫ toOne X ≫ point a₀) g]
          _ = _ := hc
    refine ⟨s, hs, ?_⟩
    intro s' hs'
    apply (map_point_bijective F (f₀ a₀)).1
    calc
      _ = F.map (point a₀).op (F.map f₀.op s') := by
        rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp,
          large_type_functor_map_eq F (point (f₀ a₀)) (point a₀ ≫ f₀)]
      _ = m₀ := congrArg (F.map (point a₀).op) (hs' f₀ hf₀)
      _ = _ := by
        change m₀ = F.map (point (f₀ a₀)).op (F.map (toOne X).op m₀)
        rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp,
          large_type_functor_map_eq F (point (f₀ a₀) ≫ toOne X) (𝟙 _), op_id, F.map_id]
        rfl
  · obtain ⟨Y₀, f₀, hf₀⟩ := hr.1
    let g : X ⟶ Y₀ := ↾fun x ↦ False.elim (hx ⟨x⟩)
    let s := F.map g.op (t f₀ hf₀)
    have hs : t.IsAmalgamation s := by
      intro Y f hf
      have hh := ht (f ≫ g) (𝟙 Y) hf₀ hf (by
        apply ConcreteCategory.hom_ext
        intro y
        exact False.elim (hx ⟨f y⟩))
      simpa [s, op_comp, F.map_comp, ConcreteCategory.comp_apply] using hh
    refine ⟨s, hs, ?_⟩
    intro s' hs'
    have hh : g ≫ f₀ = 𝟙 X := by
      apply ConcreteCategory.hom_ext
      intro x
      exact False.elim (hx ⟨x⟩)
    calc
      s' = F.map (g ≫ f₀).op s' := by rw [hh, op_id, F.map_id]; rfl
      _ = s := by
        simpa [s, op_comp, F.map_comp] using
          (congrArg (F.map g.op) (hs' f₀ hf₀))

#print axioms pair_isSheafFor
end Triangle

namespace Triangle
lemma small_type_isSheaf (F : (Type 1)ᵒᵖ ⥤ Type 0) :
    Presieve.IsSheaf pairCoverage.toGrothendieck F := by
  intro X S hS
  obtain ⟨R, hr, hrs⟩ :=
    pairCoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hS
  apply pair_isSheafFor F S.arrows
  constructor
  · obtain ⟨Y, f, hf⟩ := hr.1
    exact ⟨Y, f, hrs _ _ hf⟩
  · intro x y
    obtain ⟨Y, f, hf, a, b, ha, hb⟩ := hr.2 x y
    exact ⟨Y, f, hrs _ _ hf, a, b, ha, hb⟩

lemma all_isSheaf {D : Type*} [Category.{0} D] (F : (Type 1)ᵒᵖ ⥤ D) :
    Presheaf.IsSheaf pairCoverage.toGrothendieck F := by
  intro E
  exact small_type_isSheaf _

instance : HasSheafify pairCoverage.toGrothendieck AddCommGrpCat.{0} := by
  let inc := sheafToPresheaf pairCoverage.toGrothendieck AddCommGrpCat.{0}
  have : inc.EssSurj := ⟨fun P ↦ ⟨⟨P, all_isSheaf P⟩, ⟨Iso.refl P⟩⟩⟩
  have : inc.IsEquivalence := {}
  exact HasSheafify.mk' pairCoverage.toGrothendieck AddCommGrpCat.{0}
    inc.asEquivalence.symm.toAdjunction

instance : pairCoverage.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{0} := by
  have (P : (Type 1)ᵒᵖ ⥤ AddCommGrpCat.{0}) :
      IsIso (toSheafify pairCoverage.toGrothendieck P) :=
    isIso_toSheafify _ (all_isSheaf P)
  have : pairCoverage.toGrothendieck.HasSheafCompose (forget AddCommGrpCat.{0}) := by
    constructor
    intro F _
    exact (isSheaf_iff_isSheaf_of_type _ _).2 (small_type_isSheaf _)
  exact GrothendieckTopology.WEqualsLocallyBijective.mk'
    pairCoverage.toGrothendieck AddCommGrpCat.{0}

#print axioms all_isSheaf
end Triangle

namespace Triangle
noncomputable def rings : Sheaf pairCoverage.toGrothendieck RingCat.{0} :=
  ⟨intRings.{0}, all_isSheaf _⟩

noncomputable def moduleSheaf : SheafOfModules.{0} rings :=
  ⟨positiveConstModule (AddCommGrpCat.of ℚ), all_isSheaf _⟩

instance : Injective moduleSheaf := by
  have : Injective moduleSheaf.val := positiveConstModule_injective _
  exact sheaf_module_injective_of_presheaf_injective rings moduleSheaf

lemma module_sheaf_counterexample :
    Injective moduleSheaf ∧ Presieve.ofArrows E inclusion ∈ pairCoverage U ∧
      ¬ IsZero ((complex.cohomologyFunctor 1).obj moduleSheaf.val.presheaf) :=
  ⟨inferInstance, covering, cohomology_nonzero⟩

#print axioms module_sheaf_counterexample
end Triangle

namespace Triangle

theorem false_signature :
    ¬ ∀ (J : Precoverage (Type 1))
      [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
      (R : Sheaf J.toGrothendieck RingCat.{0})
      [HasSheafify J.toGrothendieck AddCommGrpCat.{0}]
      [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{0}]
      (I : SheafOfModules.{0} R) [Injective I]
      {T : Type 0} {U : Type 1} (f : T → Type 1) (hom : ∀ t, f t ⟶ U)
      (_ : Presieve.ofArrows f hom ∈ J U) (S : SiteCechComplex f hom)
      (p : ℕ), 0 < p → IsZero ((S.cohomologyFunctor p).obj I.val.presheaf) := by
  intro h
  exact cohomology_nonzero
    (h pairCoverage rings moduleSheaf E inclusion covering complex 1 (by decide))

#print axioms false_signature
end Triangle
```


## New nodes

lem-weil-pbc-injective-presheaf-module-cech-cocycle-lift-max states the presheaf
cocycle primitive step with hom universe v and coefficient/index universe max v w.
It follows Stacks Tags 03FC, 03AS, 03F5 and 03AT and is strictly part of the sheaf
acyclicity argument. The free-module basis is small enough in this universe.
It is needed by the five forced etale adaptations, which combine it with the
proved sheaf-to-presheaf injectivity transfer and Mathlib exactness/homology.
No new definitions are added. Change record:
coord/changes/injective-module-cech-universes.md.

## Forced adaptations

Each original module is checked against the repaired theorem before changing its
source. Original invocation blocks fail because etale homs lie in universe u,
while their rings, abelian groups, module values and indices lie in u+1. Every
adapted source compiles with identical existing signatures and visibility.
The following blocks quote the original errors and show precisely the changed
imports and proof lines; all other lines remain identical. All five modules were
unclaimed in the claim files at the time of this repair.

### Sheaf.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic

Original compiler error against the repaired interface:

```text
Application type mismatch: The argument O
has type Sheaf.{u, u + 1, u + 1, u + 2} ... RingCat
but is expected to have type Sheaf.{u, u, u + 1, u + 1} ... RingCat.
```

Changed lines (the original application cannot typecheck; the replacement
uses the strictly lower presheaf step with explicit universes u+1,u,u+1):

```diff
--- lean/Sheaf/AlgebraicGeometry/EtaleModuleInjectiveForgetAcyclic.lean
+++ lean/Sheaf/AlgebraicGeometry/EtaleModuleInjectiveForgetAcyclic.lean
@@ -10,3 +10,5 @@
 import Sheaf.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
-import Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic
+import Sheaf.CategoryTheory.Sites.InjectivePresheafModuleCechCocycleLiftMax
+import Sheaf.CategoryTheory.InjectiveModulePresheaf
+import Mathlib.Algebra.Homology.ShortComplex.Ab
 import Sheaf.AlgebraicGeometry.EtaleCechVanishingCriterion
@@ -82,6 +84,20 @@
     have hzero : IsZero ((S.cohomologyFunctor p).obj I.val.presheaf) := by
-      have h := @CategoryTheory.injective_module_cech_cohomology_isZero
-        Y.Etale _ J _ _ _ _
-      rw [show J.toGrothendieck = Y.smallEtaleTopology from htop] at h
-      exact @h O inferInstance inferInstance I inferInstance T U V f hcover S p hp
+      have : Injective I.val := injective_module_sheaf_injective_presheaf O I
+      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
+      change IsZero ((S.complex I.val.presheaf).homology (q + 1))
+      apply HomologicalComplex.ExactAt.isZero_homology
+      apply (HomologicalComplex.exactAt_iff' (S.complex I.val.presheaf)
+        q (q + 1) (q + 2) (by simp) (by simp)).2
+      rw [ShortComplex.ab_exact_iff]
+      intro c hc
+      change (CochainComplex.of.d (S.cochains I.val.presheaf)
+        (S.differential I.val.presheaf) (q + 1) ((q + 1) + 1)) c = 0 at hc
+      rw [CochainComplex.of_d] at hc
+      obtain ⟨b, hb⟩ := injective_presheaf_module_cech_cocycle_lift_max.{u + 1, u, u + 1}
+        O.obj I.val V f S q c hc
+      refine ⟨b, ?_⟩
+      change (CochainComplex.of.d (S.cochains I.val.presheaf)
+        (S.differential I.val.presheaf) q (q + 1)) b = c
+      rw [CochainComplex.of_d]
+      exact hb
     obtain ⟨c⟩ := nonempty_etale_siteCech_complex_iso Y U V f S I.val.presheaf
```

### Sheaf.AlgebraicGeometry.InjectiveEtaleModuleCechH1

Original compiler error against the repaired interface:

```text
Application type mismatch: The argument R
has type Sheaf.{u, u + 1, u + 1, u + 2} ... RingCat
but is expected to have type Sheaf.{u, u, u + 1, u + 1} ... RingCat.
```

Changed lines (the original application cannot typecheck; the replacement
uses the strictly lower presheaf step with explicit universes u+1,u,u+1):

```diff
--- lean/Sheaf/AlgebraicGeometry/InjectiveEtaleModuleCechH1.lean
+++ lean/Sheaf/AlgebraicGeometry/InjectiveEtaleModuleCechH1.lean
@@ -18,3 +18,5 @@
 import Sheaf.CategoryTheory.SiteCechMathlibComparison
-import Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic
+import Sheaf.CategoryTheory.Sites.InjectivePresheafModuleCechCocycleLiftMax
+import Sheaf.CategoryTheory.InjectiveModulePresheaf
+import Mathlib.Algebra.Homology.ShortComplex.Ab
 
@@ -93,3 +95,20 @@
     have : Injective M := hM
-    exact injective_module_cech_cohomology_isZero K R M V f hc S 1 (by decide)
+    have : Injective M.val := injective_module_sheaf_injective_presheaf R M
+    let q : ℕ := 0
+    change IsZero ((S.complex M.val.presheaf).homology (q + 1))
+    apply HomologicalComplex.ExactAt.isZero_homology
+    apply (HomologicalComplex.exactAt_iff' (S.complex M.val.presheaf)
+      q (q + 1) (q + 2) (by simp) (by simp)).2
+    rw [ShortComplex.ab_exact_iff]
+    intro c hc
+    change (CochainComplex.of.d (S.cochains M.val.presheaf)
+      (S.differential M.val.presheaf) (q + 1) ((q + 1) + 1)) c = 0 at hc
+    rw [CochainComplex.of_d] at hc
+    obtain ⟨b, hb⟩ := injective_presheaf_module_cech_cocycle_lift_max.{u + 1, u, u + 1}
+      R.obj M.val V f S q c hc
+    refine ⟨b, ?_⟩
+    change (CochainComplex.of.d (S.cochains M.val.presheaf)
+      (S.differential M.val.presheaf) q (q + 1)) b = c
+    rw [CochainComplex.of_d]
+    exact hb
   have hz := vanish R M hM
```

### Sheaf.AlgebraicGeometry.InjectiveModuleAbelianAcyclic

Original compiler error against the repaired interface:

```text
Application type mismatch: The argument O
has type Sheaf.{u, u + 1, u + 1, u + 2} ... RingCat
but is expected to have type Sheaf.{u, u, u + 1, u + 1} ... RingCat.
```

Changed lines (the original application cannot typecheck; the replacement
uses the strictly lower presheaf step with explicit universes u+1,u,u+1):

```diff
--- lean/Sheaf/AlgebraicGeometry/InjectiveModuleAbelianAcyclic.lean
+++ lean/Sheaf/AlgebraicGeometry/InjectiveModuleAbelianAcyclic.lean
@@ -12,3 +12,5 @@
 
-import Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic
+import Sheaf.CategoryTheory.Sites.InjectivePresheafModuleCechCocycleLiftMax
+import Sheaf.CategoryTheory.InjectiveModulePresheaf
+import Mathlib.Algebra.Homology.ShortComplex.Ab
 import Sheaf.AlgebraicGeometry.EtaleCechVanishingCriterion
@@ -84,6 +86,20 @@
     have hzero : IsZero ((S.cohomologyFunctor p).obj I.val.presheaf) := by
-      have h := @CategoryTheory.injective_module_cech_cohomology_isZero
-        X.Etale _ J _ _ _ _
-      rw [show J.toGrothendieck = X.smallEtaleTopology from htop] at h
-      exact @h O inferInstance inferInstance I inferInstance T U V f hcover S p hp
+      have : Injective I.val := injective_module_sheaf_injective_presheaf O I
+      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
+      change IsZero ((S.complex I.val.presheaf).homology (q + 1))
+      apply HomologicalComplex.ExactAt.isZero_homology
+      apply (HomologicalComplex.exactAt_iff' (S.complex I.val.presheaf)
+        q (q + 1) (q + 2) (by simp) (by simp)).2
+      rw [ShortComplex.ab_exact_iff]
+      intro c hc
+      change (CochainComplex.of.d (S.cochains I.val.presheaf)
+        (S.differential I.val.presheaf) (q + 1) ((q + 1) + 1)) c = 0 at hc
+      rw [CochainComplex.of_d] at hc
+      obtain ⟨b, hb⟩ := injective_presheaf_module_cech_cocycle_lift_max.{u + 1, u, u + 1}
+        O.obj I.val V f S q c hc
+      refine ⟨b, ?_⟩
+      change (CochainComplex.of.d (S.cochains I.val.presheaf)
+        (S.differential I.val.presheaf) q (q + 1)) b = c
+      rw [CochainComplex.of_d]
+      exact hb
     obtain ⟨e⟩ := nonempty_etale_siteCech_complex_iso X U V f S I.val.presheaf
```

### Sheaf.AlgebraicGeometry.InjectiveModuleSheafHCohomology

Original compiler error against the repaired interface:

```text
Application type mismatch: The argument R
has type Sheaf.{u, u + 1, u + 1, u + 2} ... RingCat
but is expected to have type Sheaf.{u, u, u + 1, u + 1} ... RingCat.
```

Changed lines (the original application cannot typecheck; the replacement
uses the strictly lower presheaf step with explicit universes u+1,u,u+1):

```diff
--- lean/Sheaf/AlgebraicGeometry/InjectiveModuleSheafHCohomology.lean
+++ lean/Sheaf/AlgebraicGeometry/InjectiveModuleSheafHCohomology.lean
@@ -8,3 +8,5 @@
 import Sheaf.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
-import Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic
+import Sheaf.CategoryTheory.Sites.InjectivePresheafModuleCechCocycleLiftMax
+import Sheaf.CategoryTheory.InjectiveModulePresheaf
+import Mathlib.Algebra.Homology.ShortComplex.Ab
 import Sheaf.AlgebraicGeometry.EtaleCechVanishingCriterion
@@ -89,6 +91,20 @@
     have hzero : IsZero ((S.cohomologyFunctor p).obj I.val.presheaf) := by
-      have h := @CategoryTheory.injective_module_cech_cohomology_isZero
-        X.Etale _ P _ _ _ _
-      rw [show P.toGrothendieck = X.smallEtaleTopology from htop] at h
-      exact @h R inferInstance inferInstance I hI T U V f hcover S p hp
+      have : Injective I.val := injective_module_sheaf_injective_presheaf R I
+      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
+      change IsZero ((S.complex I.val.presheaf).homology (q + 1))
+      apply HomologicalComplex.ExactAt.isZero_homology
+      apply (HomologicalComplex.exactAt_iff' (S.complex I.val.presheaf)
+        q (q + 1) (q + 2) (by simp) (by simp)).2
+      rw [ShortComplex.ab_exact_iff]
+      intro c hc
+      change (CochainComplex.of.d (S.cochains I.val.presheaf)
+        (S.differential I.val.presheaf) (q + 1) ((q + 1) + 1)) c = 0 at hc
+      rw [CochainComplex.of_d] at hc
+      obtain ⟨b, hb⟩ := injective_presheaf_module_cech_cocycle_lift_max.{u + 1, u, u + 1}
+        R.obj I.val V f S q c hc
+      refine ⟨b, ?_⟩
+      change (CochainComplex.of.d (S.cochains I.val.presheaf)
+        (S.differential I.val.presheaf) q (q + 1)) b = c
+      rw [CochainComplex.of_d]
+      exact hb
     obtain ⟨e⟩ := Scheme.nonempty_etale_siteCech_complex_iso X U V f S I.val.presheaf
```

### Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison

Original compiler error against the repaired interface:

```text
Application type mismatch: The argument O
has type Sheaf.{u, u + 1, u + 1, u + 2} ... RingCat
but is expected to have type Sheaf.{u, u, u + 1, u + 1} ... RingCat.
```

Changed lines (the original application cannot typecheck; the replacement
uses the strictly lower presheaf step with explicit universes u+1,u,u+1):

```diff
--- lean/Sheaf/AlgebraicGeometry/ModuleAbelianDerivedDirectImageComparison.lean
+++ lean/Sheaf/AlgebraicGeometry/ModuleAbelianDerivedDirectImageComparison.lean
@@ -14,3 +14,5 @@
 import Sheaf.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
-import Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic
+import Sheaf.CategoryTheory.Sites.InjectivePresheafModuleCechCocycleLiftMax
+import Sheaf.CategoryTheory.InjectiveModulePresheaf
+import Mathlib.Algebra.Homology.ShortComplex.Ab
 import Sheaf.AlgebraicGeometry.EtaleCechVanishingCriterion
@@ -116,6 +118,20 @@
     have hzero : IsZero ((S.cohomologyFunctor p).obj I.val.presheaf) := by
-      have h := @CategoryTheory.injective_module_cech_cohomology_isZero
-        X.Etale _ J _ _ _ _
-      rw [show J.toGrothendieck = X.smallEtaleTopology from htop] at h
-      exact @h O inferInstance inferInstance I inferInstance T U V f hcover S p hp
+      have : Injective I.val := injective_module_sheaf_injective_presheaf O I
+      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
+      change IsZero ((S.complex I.val.presheaf).homology (q + 1))
+      apply HomologicalComplex.ExactAt.isZero_homology
+      apply (HomologicalComplex.exactAt_iff' (S.complex I.val.presheaf)
+        q (q + 1) (q + 2) (by simp) (by simp)).2
+      rw [ShortComplex.ab_exact_iff]
+      intro c hc
+      change (CochainComplex.of.d (S.cochains I.val.presheaf)
+        (S.differential I.val.presheaf) (q + 1) ((q + 1) + 1)) c = 0 at hc
+      rw [CochainComplex.of_d] at hc
+      obtain ⟨b, hb⟩ := injective_presheaf_module_cech_cocycle_lift_max.{u + 1, u, u + 1}
+        O.obj I.val V f S q c hc
+      refine ⟨b, ?_⟩
+      change (CochainComplex.of.d (S.cochains I.val.presheaf)
+        (S.differential I.val.presheaf) q (q + 1)) b = c
+      rw [CochainComplex.of_d]
+      exact hb
     obtain ⟨c⟩ := Scheme.nonempty_etale_siteCech_complex_iso X U V f S I.val.presheaf
```


## Earlier second reading (a previous round; superseded)

1. Compared every delivered module with the repository version. Existing declaration
signatures and visibility are unchanged except for the explicitly recorded repaired
interface of `injective_module_cech_cohomology_isZero`; the five downstream edits are
forced adaptations and are listed in the change record.

2. Compiled the main module, the new split-off module, and all five adapted callers
with `lcompile.py`; all compiled cleanly. The only remaining `sorry` is the named
`injective_presheaf_module_cech_cocycle_lift_max` theorem, with its source, proof plan,
and DAG node recorded. No axiom, unsafe, opaque, extern, or hollow definition was
added.

3. Checked the repaired statement and the new max-universe primitive on edge cases
including q = 0, empty families and lift fibres, and zero modules/rings. The old
independent-universe statement is separately certified false; the repaired statement
has the required common-universe restrictions. Searches found no existing declaration
of the new primitive.

4. Verified the proof follows the shortest available route through injectivity transfer,
Mathlib exactness and homology, and the existing cocycle-lifting result where its
universes fit. The five larger-universe callers use the strictly lower max-universe
primitive. The unit `sk-prop-cd` route is retained; no realized unit step is bypassed.
Imports removed from callers and proof dependency updates are recorded under
`## No longer needed` and in the DAG metadata.

5. Checked the repaired item's node, the new node, proof dependencies, proof origins,
change record, forced adaptations, and report against the Lean source. The node
statements match the declarations delivered, and the new statement is strictly the
presheaf cocycle-lifting substep rather than a restatement of the item.

Changes made during this second reading: appended this review only; no proof or
interface edits were needed after compilation and comparison.


## Second reading by V2

1. Compared all seven modules with the read-only repository using diff. All five
   adapted caller signatures and visibility are byte for byte unchanged. The only
   existing interface change is the explicitly recorded universe restriction of
   `CategoryTheory.injective_module_cech_cohomology_isZero`, with old/new signatures,
   user inventory and node statement_change. No definition or Challenge target is
   changed. Verdict: passes the recorded intermediate-statement repair exception.

2. Compiled the complete seven-module set in import order with lcompile.py: no
   errors or warnings. The sole local sorry is the named public theorem
   `CategoryTheory.injective_presheaf_module_cech_cocycle_lift_max`. Scratch axiom
   checks of both main declarations report only propext, Classical.choice,
   Quot.sound and inherited/declared sorryAx. Recompiled the full old-signature
   counterexample: Triangle.false_signature has only the three permitted axioms.
   No forbidden declaration or hollow definition occurs. Verdict: valid proof
   bodies relative to the explicitly open dependencies; not axiom-free completion.

3. Read the new lemma, its full docstring proof and DAG node. The coefficient
   universe contains both the hom sets and tuple indices, so the free module
   argument stays in the category in which injectivity is assumed. For q=0 it
   uses exactness at degree 1, not at degree 0. An empty family has zero cochains;
   empty lift fibres give zero summands; a singleton lift fibre has alternating
   boundary 0,id,0,id and is exact in positive degrees. Zero modules/rings also
   cause no exception. The Type-1/small-Q counterexample is excluded. Independently
   searched LeanFinder for exact Hom complexes into injectives, Loogle for
   ShortComplex.Exact.descToInjective, launcher grep for descToInjective and
   precomposition/injectivity, and rg in Sheaf and the source library for cocycle
   lifting and universe transport. Mathlib supplies the extension step already
   used by the common-universe lemma, but no applicable larger-universe site
   cocycle theorem. ULiftHom transport would additionally require transporting
   module-presheaf injectivity and chosen products; it is not a few-minute closure.
   Verified Stacks Tags 03AS, 03AT, 03F5 and 03FC directly online. Verdict: true,
   needed presheaf substep, strictly below the ringed-site conclusion.

4. Read the exactness/homology reductions and checked every added import is
   proof-only, while public imports supply signature types. The main proof uses
   the existing injectivity transfer and common-universe lifting declaration;
   the adapted callers use the new lifting substep and an actual exactness proof.
   No whole-statement restatement replaces the item. sk-prop-cd.realized has no
   node attached to this item, and its route is retained. The removed dependency
   is now explicitly named under No longer needed. Verdict: no unsupported
   pruning or bypass; net holes closed minus added remains zero.

5. Compared each delivered node with its repository record and its Lean module.
   Main proof_deps are unchanged and match the three proof steps. Caller nodes
   replace only the invalid ringed-site dependency with injectivity transfer and
   max-universe lifting. New-node searches, source, creation, blueprint ancestry,
   statement and Lean record are present, and proof_deps are the union of step
   uses. Main statement_change lists the citing nodes and change record.
   Verdict: metadata agrees with the delivered reduction and its open lemma.

Changes in this second reading: made the removed caller dependency node explicit
under No longer needed and appended this independent review. No Lean proof,
interface, definition, import or node needed a further edit. One original item
hole is closed at the recorded corrected signature and one lower hole is added;
this is a decomposition, not a net reduction in holes.

## Forced adaptations

### Sheaf.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
Original against changed dependencies failed:
```
/tmp/forced-adaptation-97rzj98d/lean/Sheaf/AlgebraicGeometry/EtaleModuleInjectiveForgetAcyclic.lean:86:15: error: Application type mismatch: The argument
  O
has type
  Sheaf.{u, u + 1, u + 1, u + 2} Y.smallEtaleTopology RingCat
of sort `Type (u + 2)` but is expected to have type
  Sheaf.{u, u, u + 1, u + 1} Y.smallEtaleTopology RingCat
of sort `Type (u + 1)` in the application
  @h O

(with the modules compiled into /tmp/forced-adaptation-97rzj98d/.lbuild) [8.2 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.AlgebraicGeometry.InjectiveEtaleModuleCechH1
Original against changed dependencies failed:
```
/tmp/forced-adaptation-y4akvymn/lean/Sheaf/AlgebraicGeometry/InjectiveEtaleModuleCechH1.lean:94:52: error: Application type mismatch: The argument
  R
has type
  Sheaf.{u, u + 1, u + 1, u + 2} K.toGrothendieck RingCat
of sort `Type (u + 2)` but is expected to have type
  Sheaf.{u, u, u + 1, u + 1} K.toGrothendieck RingCat
of sort `Type (u + 1)` in the application
  @injective_module_cech_cohomology_isZero Y.Etale Y.instCategoryEtale K ?m.272 ?m.273 ?m.274 ?m.275 R
/tmp/forced-adaptation-y4akvymn/lean/Sheaf/AlgebraicGeometry/InjectiveEtaleModuleCechH1.lean:94:10: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  HasSheafify K.toGrothendieck AddCommGrpCat

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.

(with the modules compiled into /tmp/forced-adaptation-y4akvymn/.lbuild) [6.4 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.AlgebraicGeometry.InjectiveModuleAbelianAcyclic
Original against changed dependencies failed:
```
/tmp/forced-adaptation-u9x96okk/lean/Sheaf/AlgebraicGeometry/InjectiveModuleAbelianAcyclic.lean:88:15: error: Application type mismatch: The argument
  O
has type
  Sheaf.{u, u + 1, u + 1, u + 2} X.smallEtaleTopology RingCat
of sort `Type (u + 2)` but is expected to have type
  Sheaf.{u, u, u + 1, u + 1} X.smallEtaleTopology RingCat
of sort `Type (u + 1)` in the application
  @h O

(with the modules compiled into /tmp/forced-adaptation-u9x96okk/.lbuild) [4.2 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.AlgebraicGeometry.InjectiveModuleSheafHCohomology
Original against changed dependencies failed:
```
/tmp/forced-adaptation-x41ae2rq/lean/Sheaf/AlgebraicGeometry/InjectiveModuleSheafHCohomology.lean:93:15: error: Application type mismatch: The argument
  R
has type
  Sheaf.{u, u + 1, u + 1, u + 2} X.smallEtaleTopology RingCat
of sort `Type (u + 2)` but is expected to have type
  Sheaf.{u, u, u + 1, u + 1} X.smallEtaleTopology RingCat
of sort `Type (u + 1)` in the application
  @h R

(with the modules compiled into /tmp/forced-adaptation-x41ae2rq/.lbuild) [5.5 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
Original against changed dependencies failed:
```
/tmp/forced-adaptation-u1h9esgn/lean/Sheaf/AlgebraicGeometry/ModuleAbelianDerivedDirectImageComparison.lean:120:15: error: Application type mismatch: The argument
  O
has type
  Sheaf.{u, u + 1, u + 1, u + 2} X.smallEtaleTopology RingCat
of sort `Type (u + 2)` but is expected to have type
  Sheaf.{u, u, u + 1, u + 1} X.smallEtaleTopology RingCat
of sort `Type (u + 1)` in the application
  @h O

(with the modules compiled into /tmp/forced-adaptation-u1h9esgn/.lbuild) [7.7 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
