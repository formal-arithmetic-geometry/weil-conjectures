## Worker report

Module `Sheaf.AlgebraicGeometry.Picard.SigmaKPoints` states
`AlgebraicGeometry.bijective_picardFunctorNormalized_kPoints`, with proof `sorry`.
It states bijectivity of the canonical map, rather than existence of an unspecified
bijection: forget normalization and pull back along the inverse of the first
projection `X ×_k Spec k → X`. No definition or further node is needed.

Hypothesis and clause matching:
- “k a field”: `(k : Type u) [Field k]`.
- “X a scheme over k”: `(X : Scheme.{u}) [X.Over (Spec (.of k))]`.
- “σ ∈ X(k)”: `(σ : Spec (.of k) ⟶ X)` and
  `(hσ : σ ≫ (X ↘ Spec (.of k)) = 𝟙 (Spec (.of k)))` state precisely that
  σ is a k-morphism, i.e. a section of the structure map.
- “Pic_{X/k,σ}(k)”: the domain is
  `(picardFunctorNormalized (X ↘ Spec (.of k)) σ hσ).toFunctor.obj
  (.op (Over.mk (𝟙 (Spec (.of k)))))`. The test scheme is Spec k with
  its identity structure map. Its elements are classes, not trivialized bundles.
- “= Pic(X) canonically”: `Function.Bijective` of the explicitly specified
  function `L ↦ Scheme.Pic.map (inv (pullback.fst ... (𝟙 ...))) L.val`.
  Here `L.val` forgets normalization and is a Picard class on the base change;
  `Scheme.Pic.map` transports it to `X.Pic`. The first projection is an
  isomorphism because the base-change morphism is the identity. Thus the
  assertion is the canonical identification in the node, not an arbitrary
  equivalence. The node concerns sets of isomorphism classes, as its normalized
  functor definition specifies; no additional group or trivialization data is asserted.

Dependency declarations read and used:
- `def-pc-pic-sigma-functor`: `AlgebraicGeometry.picardFunctorNormalized`,
  module `WeilConjectures.AlgebraicGeometry.Picard.Defs`, imported directly.
  Its full definition is a subfunctor of `picardPresheaf`, imposing
  `Pic.map (sectionBaseChange ...) L = Pic.mk (SheafOfModules.unit ...)`.
- `def-pc-base-change`: module `Sheaf.AlgebraicGeometry.BaseChangeConventions`
  and its declarations/docstrings were read. Its record explicitly instructs
  citers needing X_T to use `CategoryTheory.Limits.pullback f T.hom`, with
  `pullback.fst` the projection to X. This is used directly here; the module's
  module-base-change and geometric-fibre definitions are not used, so it is
  not redundantly imported. This is a usable dependency, not a missing notion.
- `def-sc-picard-group`: `AlgebraicGeometry.Scheme.Pic`, module
  `WeilConjectures.AlgebraicGeometry.PicardFunctor`, imported transitively.
  The definition is invertible classes in the skeleton of X.Modules, valid
  for arbitrary schemes. Its pullback operation `Scheme.Pic.map` is reused.
- Mathlib `CategoryTheory.Limits.pullback_fst_iso_of_right_iso` supplies the
  isomorphism instance for the first projection; `CategoryTheory.inv` names
  its inverse. The definitions and signatures were read in Pullback/Iso.lean.

Source and edge cases:
The blueprint source was read on the project server via read-only SSH because
literature/blueprint is absent on this machine. Its statement is identical to
the node. The imported blueprint proof calls σ a closed immersion, which is
unnecessary; the node's already-reviewed proof removes that assertion. The
module docstring follows that corrected node proof step by step. Any field,
including positive characteristic and non-algebraically-closed fields, is
allowed. No smoothness, properness, finite type, separatedness, connectedness,
or closed-immersion assumption occurs. For X = Spec k and σ the identity both
sets have one class. An empty X has no such section, so its exclusion follows
from the stated rational-point hypothesis. No index family occurs. Universes
are explicit: k and schemes lie in universe u, and Picard classes retain the
source's universe u+1; no independent test universe or smallness restriction
is imposed. No statement correction or dispute is needed.

Searches for an existing statement (recorded also in searches.jsonl):
- LeanFinder: “Normalized Picard functor at Spec of a field canonically equals
  Picard group of scheme”: eight hits, including CommRing.relPic,
  CommRing.relPic_eq_top, and ring Picard/class-group results; no scheme-normalized
  functor statement.
- Loogle: `CommRing.Pic, Field`: zero hits.
- msearch grep: `picardFunctorNormalized.*Pic|Pic.*picardFunctorNormalized`
  in Mathlib AlgebraicGeometry: zero hits.
- LeanSearch: “Normalized Picard functor evaluated at the base field equals
  Picard group”: unavailable (Internal Server Error), no verdict inferred.
- rg of WeilConjectures and lean/Sheaf for normalized Picard / sigma Picard
  declarations, and the item id: the definition and existing general comparison
  statements occur, but no declaration of this statement. In particular,
  `bijective_toPicardFunctor_picardFunctorNormalized` requires IsIso of
  pushforwardUnitMap and identifies with the sheafified functor; it is not this
  unconditional identification with X.Pic.
- rg of dag/lean_names_upstream.json: normalized-functor declarations exist,
  but this item and the proposed full declaration name have no match.
- rg of Mathlib, WeilConjectures and lean/Sheaf for the proposed full short name:
  no collision.

Validation: server single-file compile passed in 2.4 seconds with no errors
or warnings. The theorem proof remains `sorry`, as stage 2 requires.

## Second reading by E1

I independently read the sandbox node and module, all three statement dependency
nodes, and their source declarations. I read the blueprint source on the server
by read-only SSH: `sec-picard-framework/sk-def-picard-pic/lem-pc-sigma-k-points.md`,
its unit `_section.md`, and the chapter `_section.md`. The lemma's source is a
blueprint lemma, not a Stacks-tag lemma. The surrounding unit distinguishes the
normalized kernel functor from the fppf-sheafified Picard functor. The universal
pushforward-unit-isomorphism hypothesis applies to their comparison, not to this
lemma. The chapter imposes no further hypothesis on this lemma.

The complete object/hypothesis/conclusion checklist, matched to the Lean:

1. A field k: `(k : Type u) [Field k]`. Exactly the field hypothesis; no
   algebraic-closure, characteristic, cardinality, or finiteness assumption. PASS.
2. A scheme X over k: `(X : Scheme.{u}) [X.Over (Spec (.of k))]`.
   Its structure morphism is `X ↘ Spec (.of k)`. No smoothness, properness,
   separatedness, integrality, connectedness, or finite-type instance is added.
   PASS.
3. A rational point sigma of this k-scheme: `(σ : Spec (.of k) ⟶ X)` and
   `hσ : σ ≫ (X ↘ Spec (.of k)) = 𝟙 (Spec (.of k))`.
   This is exactly a section of its structure morphism, not an arbitrary
   scheme point. No closed-immersion hypothesis is included. PASS.
4. Evaluation at k: the functor object is
   `(picardFunctorNormalized (X ↘ Spec (.of k)) σ hσ).toFunctor.obj
   (.op (Over.mk (𝟙 (Spec (.of k)))))`.
   `Over.mk` has underlying scheme Spec k and the identity structure morphism;
   `picardPresheaf` evaluates to `(pullback f T.hom).Pic`.
   The normalized functor's `obj` predicate is precisely
   `Pic.map (sectionBaseChange f σ hσ T) L = Pic.mk (SheafOfModules.unit ...)`.
   Thus these are classes with trivial pullback, with no chosen trivialization.
   PASS.
5. Pic(X): the codomain of `Scheme.Pic.map` along the inverse first projection
   is `X.Pic`. `Scheme.Pic` in PicardFunctor.lean:167 is the subtype of invertible
   classes in the skeleton of X.Modules. Though the dependency node introduces
   this notion for a curve, its recorded declaration works for all schemes,
   as this lemma requires. PASS.
6. Canonical identification, and every clause of the conclusion:
   `Function.Bijective (fun L ↦ Scheme.Pic.map
   (inv (pullback.fst (X ↘ Spec (.of k)) (𝟙 (Spec (.of k))))) L.val)`.
   Here L.val forgets the normalization predicate, yielding a Picard class on
   X times_k Spec k; it does not extract the skeleton class inside that class.
   The first projection is an isomorphism by Mathlib's
   `pullback_fst_iso_of_right_iso` (Pullback/Iso.lean:115), since the right map
   is the identity. Its inverse has direction X to the base change, so the
   contravariant `Scheme.Pic.map` has the required direction to X.Pic.
   This is the specified canonical identification, expressed on the existing
   set-valued functor, not merely existence of an unspecified bijection. All
   inputs are universally quantified before bijectivity; no additional clause
   or existential choice is introduced. PASS.

Dependency check: `sectionBaseChange` (Defs.lean:81) is the universal pullback
lift of `T.hom ≫ σ` and the identity; `picardFunctorNormalized` (Defs.lean:228)
is the exact kernel described by its node. `Scheme.Pic.map`
(PicardFunctor.lean:245) is pullback of invertible sheaf classes. I also opened
BaseChangeConventions.lean: its module text explicitly reuses `pullback`,
`pullback.fst`, `baseChangeMap`, and `sectionBaseChange` for these notions.
There is no need to import that module's unrelated fibre or module-base-change
statements. The existing declaration is usable; no private replacement or
missing definition is involved. No new nodes or dependency modules are delivered.

Edge cases: for X = Spec k with the identity section, both sides have one class;
this matches `Scheme.pic_of_field` in the project's PicardOfField.lean. The
structure-sheaf class is included and maps to the structure-sheaf class. An
empty scheme has no k-section because Spec of a field is nonempty; it is
excluded by precisely the stated rational-point hypothesis. Arbitrary
nonempty disconnected schemes, nonreduced schemes, and positive characteristic
are allowed. Empty index sets and n = 0 do not arise in this statement. The
universe u is explicitly bound, with schemes and field in the common ambient
universe required by the recorded scheme/Picard functor declarations and
Picard classes in Type (u+1). This works at every ambient universe; there is no
independent lower test-scheme universe, no smallness premise, and no unbound
universe or variable.

Independent searches, with wording different from the worker's queries:
- LeanFinder: "The kernel of pullback of line bundles along a rational section
  at the base field is canonically the whole Picard group". Eight hits included
  Submodule.ker_unitsToPic and CommRing.relPic, and unrelated ideal-kernel facts.
  None states this scheme-functor identification.
- Loogle: `CommRing.Pic, Subsingleton`. Eight hits, including the local-ring
  triviality instance and CommRing.relPic_eq_top. These concern module Picard
  groups of rings, not the scheme-valued normalized functor.
- LeanSearch: "Pullback of invertible sheaves along a rational point is trivial
  and the normalized Picard classes over the field equal all line bundle
  classes". Service returned Internal Server Error. Recorded as unavailable;
  no conclusion was inferred from it.
- msearch grep: `sectionBaseChange.*(Bijective|Equiv)|Pic.*(Spec|Field)`.
  Hits were irrelevant to this theorem. Direct rg over Mathlib's
  AlgebraicGeometry and RingTheory/PicardGroup.lean, all upstream Picard
  modules, and the project's Picard modules used
  `picard.*(kpoints|k_points|field|spec)|normalized.*(biject|equiv)|sigma.*points`.
  I opened the closest upstream signatures: Defs.lean:671 compares to the
  sheafified functor with the extra universal pushforward-unit-isomorphism
  assumption; RationalPoint.lean:91 compares functors for smooth proper
  geometrically integral curves. Neither is this unconditional identification
  with X.Pic. The project's PicardOfField.lean states only triviality of
  Pic(Spec k). The proposed theorem name and item id have no match in
  dag/lean_names_upstream.json. There is no duplicate statement to record
  as existing.

Faults and changes: no mismatch was found, and the Lean and node record are
unchanged. Only this independent second-reading section and search records
were added. The source proof's description of sigma as a closed immersion is
unnecessary for general X; the node proof already correctly removes it, and
this module's proof docstring follows that corrected proof: identify the base
change and section, describe the kernel, apply lem-pc-pic-of-field to every
pullback, then forget normalization and transport along the canonical
projection. No stage-2 statement correction is needed. Every declaration
has its source and blueprint docstring; the sole theorem retains proof
`sorry`, there are no definitions or file-local notation/instances, and the
import is used by the statement. Lines satisfy the 100-character limit.

Second-reader validation: `scompile.py E1 lem-pc-sigma-k-points` compiled the
single delivery module on the server in 2.0 seconds, exit code 0, with no
warnings or errors. The node's lean.statement was checked against the exact
signature in the file and agrees verbatim up to the proof delimiter.
