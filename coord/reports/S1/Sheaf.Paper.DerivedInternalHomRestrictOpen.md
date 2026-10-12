## What changed

Replaced the sole `sorry` in `Sheaf.Paper.DerivedInternalHomRestrictOpen` with a
complete Lean proof of `CategoryTheory.derivedInternalHom_restrict_open`.
Its signature and both public imports are unchanged.

The proof chooses complex representatives via essential surjectivity of
`DerivedCategory.Q`, constructs the source library's functorial K-injective
replacement of the second representative, and obtains its representative
isomorphism by inverting the localized resolution map. It applies the existing
`derivedInternalHom_obj_iso` globally and on the localized site. The existing
`kInjective_of_restrict_open` makes the restricted target K-injective.
`mapDerivedCategoryFactors` transports the representative isomorphisms through
exact restriction. The last step is an explicit composition of the two
computation isomorphisms, the localized ordinary chain isomorphism, and the
exact-functor comparison. No representative is selected from an unproved mere
existence result, and there is no new definition.

Added the proof import `Sheaf.Algebra.Homology.HomComplexRestrictOpen`. This new
module states the ordinary, underived chain-isomorphism part of the argument,
with its complete proof in words and its own DAG node. Updated the original
node's proof, proof dependencies and proof origin to match the Lean assembly.

Validation: both delivered modules compile together using `lcompile.py --all`
without errors or warnings. The item's final proof compiles in about nine
seconds. All final Lean lines have at most 100 characters. The module-import
closure comparison below is a source traversal, not a global build or a claim
that these modules are unreachable from every other target branch.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.derivedInternalHom_restrict_open`
(node `lem-sc-derived-internal-hom-restrict-open`). No `sorry` remains in the
item's module.

Added exactly one hole:
`CategoryTheory.homComplex_restrict_open`
(node `lem-sc-hom-complex-restrict-open`), in
`Sheaf.Algebra.Homology.HomComplexRestrictOpen`. Its proof is exactly `:= by sorry`.
There are no other delivered holes, private unfinished helpers, or holes in
any definition.

This is a decomposition: one upper hole closed, one strictly smaller ordinary
chain-isomorphism hole added. It is not an independent proof of the whole
mathematical result. The remaining statement involves only two arbitrary
complexes and open restriction; it does not involve derived categories,
K-injectivity, quasi-isomorphisms, resolutions, or representative choices.
The original theorem's construction of the resolution, its restriction,
the two derived-Hom computations and the composition are all checked Lean.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`: its chosen generator
  and degreewise-injective resolution assertion are unnecessary. The proved
  generic source resolution construction already exposed by
  `DerivedInternalHom` supplies exactly the required replacement.
- `Sheaf.Algebra.Homology.HomComplex`: already publicly available through
  `DerivedInternalHom`; the proof still uses its `homComplex` declaration.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`: ordinary
  sheaf-Hom restriction is now confined to the new lower module, whose proof
  plan imports `InternalHomOver`. This source module remains transitively
  reachable and is not globally pruned.

The following four modules disappear from this item's source import closure
when the delivered files replace the originals:

- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
- `Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`
- `Mathlib.Algebra.DirectSum.Finsupp`

The original direct proof dependency
`prop-pur-kinjective-resolutions-exist` is replaced by the already proved
`lem-weil-pbc-kinjective-functorial-existence`; the specialized generator and
injective-term assertions are not used. Its specialized supporting nodes
`lem-pur-ringed-site-grothendieck-abelian`,
`lem-pur-kinjective-degreewise-existence`, and
`lem-pur-kinjective-functorial-injective` are not needed on this proof route.
They may remain needed elsewhere. The other removed original direct
`proof_deps` entry is `def-pur-sheaf-hom`: its use moves to the new ordinary
Hom-complex node, so it is not transitively pruned. The Hom-complex definition and
open K-injective restriction lemma remain needed.

## Where the brief, the DAG or earlier work was wrong

There is no disputed statement or source error. Read Stacks Tag 08DL at
https://stacks.math.columbia.edu/tag/08DL; the local literature checkout on
this machine contains only the tracked literature lists, not cohomology.tex.
The source proof reduces to the construction and K-injective restriction,
as does the delivery. The unit `sk-thm-picard-duality` has no realized node
bindings here; no unit statement or proof route was bypassed.

The original Step 3 calls the ordinary Hom-complex restriction identification
elementary, but none of its named dependencies provides that chain isomorphism
as a Lean declaration. `SheafOfModules.overHomObjIso` provides its individual
sheaf-Hom factors. The new node isolates precisely the missing product and
differential compatibility, rather than repeating the derived statement.

Tried the degreewise product/projection approach using
`Classical.choose_spec (homComplex_exists ...)`, limit preservation by open
restriction, and `overHomObjIso`. The expensive part was reducing the fully
faithful sheaf comparison with its `eqToIso` carrier transports when expressing
its compatibility with pre- and post-composition. Several exploratory compiles
hit the heartbeat or 60-second limit. These exploratory bodies are not in the
delivery. The next worker can obtain both chosen sets of product projections
from `homComplex_exists`, prove the factor comparison's naturality through
`PresheafOfModules.restrictOverHomObjIso_hom_app_apply`, then compare the
signed differentials using the second conjunct of the chosen specification.
The product preservation argument needs explicit universe shrinking for the
integer-indexed products, rather than relying on typeclass inference to shrink
`PreservesLimitsOfSize.{u,u}` to `{0,0}`.

LeanSearch was unavailable with an Internal Server Error. LeanFinder, Loogle,
Mathlib grep, library searches and whole-DAG duplicate searches were completed
and recorded in the new node; no existing ordinary Hom-complex restriction
statement was found. No infrastructure change or forced adaptation was made.

## New nodes

`lem-sc-hom-complex-restrict-open` is Step 3 of the original proof: restriction
commutes with the ordinary sheaf Hom complex for arbitrary unbounded complexes.
Its three proof steps spell out preservation of the product terms, restriction
of each internal sheaf Hom, and compatibility with the signed differential.
It inherits the parent's chapter and unit and cites the original Stacks
construction, the localized-site definition and the Hom-complex/sheaf-Hom
nodes. Empty opens and zero or unbounded complexes require no extra hypotheses;
products need only be preserved, not exact. This is strictly the underived
part of the argument. No change record is required because every existing
signature and definition is unchanged.


## Second reading by S1

1. Compared the complete item module with the repository using `diff -u`.
   The only differences are three removed plain proof imports, the new plain
   HomComplexRestrictOpen import, and the replacement proof. The theorem
   signature, public imports, visibility and existing definitions are byte for
   byte unchanged. The only additional module has its own new theorem and node;
   no change record or forced adaptation is required. Verdict: pass.
2. Compiled both delivered modules in import order using `lcompile.py --all`:
   clean, approximately 1.9 and 8.5 seconds. A scratch copy with `#print axioms`
   for CategoryTheory.derivedInternalHom_restrict_open and
   CategoryTheory.homComplex_restrict_open compiled and reported exactly
   propext, Classical.choice, Quot.sound and sorryAx for each. The scratch copy
   was removed. The sole delivered sorry is the listed ordinary comparison;
   there is no forbidden declaration, proof bypass, private unfinished helper
   or new definition. The resolution is the existing small-object-argument
   construction, not an arbitrary choice from an unproved existence assertion.
   The representatives of Q are determined up to the isomorphism used here.
   Verdict: pass as a decomposition, not a sorry-free derived theorem.
3. Read Stacks 08DL (https://stacks.math.columbia.edu/tag/08DL) and the product
   formula and signed differential of 0A8X
   (https://stacks.math.columbia.edu/tag/0A8X), the actual homComplex_exists
   specification, and SheafOfModules.overHomObjIso in InternalHomOver.
   The new statement has exactly arbitrary integer cochain complexes on X
   and an arbitrary open U; the localized ring and both restriction functors
   agree with the node. Termwise products and local linear maps restrict
   without changing either differential summand. Empty U has the zero module
   sheaf; zero complexes give zero terms; U equal to the whole space gives
   the usual slice equivalence; unbounded complexes retain all integer
   factors. No exactness of infinite products is assumed. This is strictly
   the ordinary chain-comparison step, with none of the derived or resolution
   assertions of the parent. Its docstring gives the full mathematical
   argument and its node records the necessary sources. Independent searches
   used LeanFinder with "exact restriction functor ... products ... internal
   Hom cochain complex", Loogle with "homComplex", and rg with both orders
   of homComplex/restriction/overFunctor in Mathlib and both library roots.
   No existing sheaf-valued chain comparison was found; Mathlib's HomComplex
   concerns ordinary morphism cochains. Verdict: pass; closing the lower hole
   is not a short existing-lemma application.
4. Traced the proof from the top: Q representatives, the concrete functorial
   resolution and its quasi-isomorphism, global computation eX, restricted
   K-injectivity, the two exact-functor comparison isomorphisms, local
   computation eU, and the four correctly oriented final isomorphisms.
   The generic resolution is a shorter route than the specialized
   degreewise-injective resolution. The two public imports supply the
   statement's objects, exact restriction and required instances; the two
   plain imports supply precisely the proof inputs. The lower module's
   public imports supply its Hom complex and additive restriction signature;
   its plain InternalHomOver import is the recorded lower proof input.
   Checked every old proof_deps entry: specialized resolution removed,
   sheaf Hom moved to the lower node, other three retained. Checked the
   unit sk-thm-picard-duality, whose realized statement and step arrays have
   no bindings; no fixed unit route changes. Verdict: pass.
5. Opened both delivered JSON nodes and the functorial-existence dependency.
   Each proof_deps is exactly the union of its steps' uses. The existing
   node's three steps match the Lean assembly; its proof_origin records
   the Stacks route and S1 assembly. The new node has self-contained
   statement and statement dependencies, source, explicit product/factor/
   differential proof steps, search records, split status, created record,
   blueprint ancestry, inherited chapter/unit and verbatim Lean signature.
   No node or statement outside the delivery was changed. Verdict: pass.

Second reading changed only this report: clarified that def-pur-sheaf-hom
is removed from the parent's direct proof dependencies but retained through
the lower node, and recorded the independent checks above. No Lean repair
or additional split was necessary. One original hole closed and one lower
hole added; net zero holes for this decomposition, before any maintainer
ledger calculation of the pruned import closure.
