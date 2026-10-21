## Worker report

The delivery states `AlgebraicGeometry.Scheme.adicPerfectModel_complete_reduction` in
`Sheaf.Paper.AdicPerfectModelCompleteReduction`. Its only theorem proof is `sorry`.
The ten helpers have real data: they abbreviate or apply existing constant realization,
ordinary scalar extension, module sheafification, cohomology, slice restriction, or the
precise conclusions and normalization formulas of this same node. The repair adds one definition node recording existing coefficient constructions;
there are no dependency-module repairs and no statement correction.

Source read: Bhatt--Scholze, *The pro-etale topology for schemes*, Proposition 6.6.11,
its explanation of “locally constant with perfect values” and the reverse implication of
its proof. The source identifies the local model with the completed constant perfect
complex, proves completeness locally, and identifies its residue with the constant
perfect residue value. The seven detailed proof steps of this node are reproduced in
the theorem docstring, including their finite-idempotent calculation and slice argument.
The node's source field incorrectly associates bounded-flat-K-flat with Tag 06YS; the
correct tag is 06YQ, already used in its proof step 4 and in this module's docstrings.
This is a source-reference typo, not a statement defect; source is left unchanged.

Hypothesis and clause matching:

* Scheme T: `(T : Scheme.{u})`. No Noetherian, dimension, affine or nonempty hypothesis on T.
* Arbitrary commutative Noetherian A: `(A : Type (max v (u + 1))) [CommRing A]
  [IsNoetherianRing A]`. The independent coefficient universe v avoids bounding A by the
  scheme universe. This is the existing coefficient-sized small-site convention.
* Maximal ideal I: `(I : Ideal A) (_hI : I.IsMaximal)`. No uniqueness of the maximal ideal,
  localness or completeness of A is assumed.
* The residue field k=A/I is written `A ⧸ I ^ (0 + 1)`. Positive tower exponents are indexed
  n+1, so this is exactly A/I, not A/I^0. Maximality makes it a field mathematically;
  `Module.Finite` expresses finite-dimensionality without introducing another field datum.
* The site is `coefficientProEtaleModelTopology.{u,v} T`, on
  `coefficientProEtaleSiteModel.{u,v} T`. These are the existing AsSmall equivalence and
  induced topology of T.ProEt. The native site still has object universe u+1 and morphism
  universe u. This changes neither the site nor its covering slices.
* B is `ConstantCompletion.completed J A I`, the actual limit of
  `ConstantCompletion.finite J A I n`, with the quotient transition maps and n meaning n+1.
  Its canonical constant-to-completed map is `ConstantCompletion.coefficientMap J A I`.
* The bounded coefficient complex is `P : CochainComplex (ModuleCat A) ℤ`.
  `_hbounded : ∀ q, q < a ∨ b < q → IsZero (P.X q)` says exactly zero terms outside [a,b].
  `_hP : ∀ q, Module.Finite A (P.X q) ∧ Module.Projective A (P.X q)` supplies precisely
  finite-projective terms. There is no extra perfectness assumption on a chosen derived
  object: these hypotheses already give the representative required by
  `DerivedCategory.IsPerfectRingComplex`.
* M is `AdicPerfectModel.model J I P`: apply the recorded
  `commutativeSiteConstantModuleFunctor` termwise and then the actual
  `ConstantCompletion.change (coefficientMap J A I)` termwise. This is B tensor_A P,
  not a chosen module with a postulated identification.
* `HasCompleteResidueCalculation` first asserts `ConstantCompletion.IsComplete π (Q.obj M)`
  for π the first completed-ring projection. This is the recorded
  `IsLocallyDerivedRingedIdealComplete` predicate at the kernel ideal of π, with its
  internal Hom on every slice and every ideal section. The Noetherian quotient
  identification `ConstantCompletion.flat_and_quotients` identifies this kernel with IB.
* The ordinary residue is `algebraicResidue I P`, termwise
  `ModuleCat.extendScalars (Ideal.Quotient.mk (I^(0+1)))`. `constantResidue` is its actual
  constant complex. Scalar extension orders its tensor factors as k tensor_A P; the
  canonical symmetry identifies this with the node's P tensor_A k.
* The existential `c` is a chain isomorphism from the ordinary residue of M to that
  constant residue. `IsResidueComparison ... c.hom` fixes it on local tensor generators:
  c tensor (b tensor p) maps to c*bar(b) times the constant section 1 tensor p.
  These generators locally generate, so this specifies the canonical map, rather than
  an arbitrary isomorphism between the two objects.
* The `IsIso` clause in `HasCompleteResidueCalculation` is on the composite
  `extendComparison π |>.app M` followed by `Q.map c.hom`. Its source is exactly
  `(ConstantCompletion.extend π).obj (Q.obj M)` and its target is the localization of
  the constant algebraic residue complex. Thus it states the canonical derived residue
  isomorphism with the universal K-flat counit retained. An isomorphism is equivalently
  an invertible morphism; no extra comparison map is assumed.
* For every q, the separate `Module.Finite k ((algebraicResidue I P).homology q)` gives
  finite-dimensionality of the precise algebraic cohomology value. The `Nonempty` in
  `HasCompleteResidueCalculation` identifies the actual derived residue cohomology
  with `commutativeSiteConstantModuleFunctor J k` applied to this same value.
* The final part of `HasCompleteResidueCalculation` gives `IsZero` for the cohomology of
  Q(M) and its derived residue whenever q<a or b<q, with exactly the original bounds.
* For every site object U (hence every object in a covering), `overComplex` applies the
  existing `SheafOfModules.overFunctor` termwise. The coefficient map is the actual
  `overPullback CommRingCat U` image of π, so the coefficient is B restricted to the slice.
  The existential slice chain isomorphism d has `IsSliceResidueComparison ... d.hom`,
  the identical tensor formula evaluated at each object of Over U. The same
  `HasCompleteResidueCalculation` then gives local derived completeness, the canonical
  derived residue isomorphism, the restricted constant cohomology sheaf and both degree
  bounds on that slice. In particular d is normalized, not an arbitrary slice isomorphism.
* No `Finite k`, regularity, quotient-perfectness, residue-characteristic, completeness of
  A, or other hypothesis occurs. Every variable and universe is explicitly bound, with
  `set_option autoImplicit false`.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its category;
  `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `ProEt.topology`.
* `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; the ideal and quotient notions
  are Mathlib's, and projectivity is `Module.Projective` from
  `Mathlib.Algebra.Module.Projective`.
* `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
* `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`, with its bounded finite-projective definition.
* `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, an abbreviation of
  `SheafOfModules`; `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory.standard` and `DerivedCategory.Q`.
* `Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete`:
  `IsLocallyDerivedRingedIdealComplete`; this is used by the existing
  `ConstantCompletion.IsComplete`, not copied into this module.
* `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `nonempty_derivedChangeOfRingsCochainModel`. The recorded universally specified derived
  pair is already exposed by `ConstantCompletion.extend` / `extendComparison`.
* `Sheaf.Paper.ConstantCompletionEquivalence`: the fourteen coefficient declarations
  recorded by `def-sfb-constant-completion-coefficient-data` supply `finite`, `completed`,
  `projection`, `coefficientMap`, `Mod`, `Cx`, `D`, `Q`, `change`, `DerivedExtension`,
  `derivedExtension`, `extend`, `extendComparison` and `tensorSection`. The existing
  `def-sfb-quotient-kernel-completeness` supplies `kernelIdeal` and `IsComplete`. These two
  definition nodes are statement dependencies; `lem-weil-pbc-constant-completion-equivalence`
  remains a proof dependency for `flat_and_quotients` and the equivalence, and is not a
  statement dependency.
* `Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor`:
  `commutativeSiteConstantModuleFunctor` and its exact/additive interface. Its landed
  node `def-sfb-site-derived-constant-module-functor` is added to stmt_deps.
* `Sheaf.AlgebraicGeometry.ProEtaleInverseImage` and
  `ProEtaleCoefficientPullbackUniverses`: the existing equivalent small-site construction;
  `coefficientProEtaleSiteModel` and `coefficientProEtaleModelTopology`.
  Their owning node `def-weil-proetale-inverse-image` is added to stmt_deps.
* The proof imports are the recorded modules for constant-section properties,
  module-sheaf sectionwise limits, torsion-limit completeness, restriction of completeness,
  the constant-completion equivalence, sheaf tensor, bounded-above-flat K-flatness,
  weakly-etale localization, restriction preserving K-flatness and tensor restriction.
  No proof dependency import creates a cycle.

Searches actually run with msearch.py (group NY, this item):

* leanfinder: `bounded finite projective complex over completed constant ring sheaf is
  derived complete and residue is constant complex` — eight results on condensed modules
  and K-projectives, no exact match.
* loogle: `Module.Finite, Module.Projective` — twelve results, including finite-projective
  splitting and dual tensor/Hom equivalences, no completed-sheaf statement.
* grep: `completed.*(perfect|projective)|perfect.*complet` — nine unrelated Mathlib
  topology/hierarchy results, no exact match.
* leansearch: `derived complete completed constant sheaf finite projective complex residue
  reduction` — eight results on constant sheaves and projective resolutions, no exact match.
* Direct rg searches of `lean/WeilConjectures` and `lean/Sheaf` for the item id, the new
  declaration names, perfect/completed models and completion gave no existing declaration
  of all clauses. They found CompletedConstantSheafReduction, AdicStratifiedPerfect,
  ConstantCompletionEquivalence and AdicResidueLiftComparisons. Their constructions were
  read. The downstream stratified-perfect theorem is not imported. The generic exact
  constant realization and completion constructions are reused directly, with no private
  replacement notion. Direct Mathlib source searches read extendScalars, its additive
  adjunction, constantSheaf, Scheme, and the derived-category localization definitions.

Edge cases checked before and after drafting: empty T; P=0; zero ranks in any degree;
a>b (all terms forced zero); a=b; an infinite residue field; a field A with I=0;
nonregular A=k[epsilon]/epsilon² with I=(epsilon); noncomplete A=Z_(p);
arbitrarily large coefficient universe; the empty slice object. None requires excluding
an index, choosing a basis, requiring a nonempty site, or bounding the cardinality of k.
A zero ring has no maximal ideal, so it is already excluded exactly by the stated
maximality hypothesis. No STATEMENT-DISPUTED issue remains.

Validation: scompile.py compiled both the sandbox module and the library-named module
cleanly under the standard 60-second limit, with no errors or warnings (7.1 s and 6.2 s
in the final run before metadata generation). All helper definitions contain real data;
there is exactly one postponed theorem. No source-library file or shared clone was edited.

## Second reading by NY

I reopened the node, its seven proof steps, the source's reverse implication and the
completed module for a separate clause-by-clause pass. This is the worker's second pass;
the independent mathematical review is the maintainer's review of this delivery, as
specified by the dispatcher brief, which forbids starting other agents.

The checks found and repaired one substantive presentation issue in the first draft:
the preliminary slice isomorphism had not retained its canonical normalization, so
`IsSliceResidueComparison` was added. I also rechecked the independent coefficient-universe
model, which had been selected before drafting; the theorem uses it throughout. A
namespace-closing error and overlong lines were repaired during compilation, and the
resulting compile has no warnings.

In the final text, I checked that the completion kernel is the residue-projection kernel
already identified with IB, that M is ordinary termwise extension (no derived A-tensor
silently substituted), that the residue source is the universal derived B-change rather
than an unrelated object, that the comparison formula has the correct c*bar(b) scalar,
that the constant cohomology value is exactly H^q(k tensor_A P), and that both global
and slice degree bounds use the original a and b without imposing a<=b. Each slice
retains B.over U, its own actual projection, its own universal counit, and the original
constant cohomology restricted to that slice. No omitted clause or extra mathematical
hypothesis was found. The helpers do not conceal an extra assumption or a sorry-defined
object. The four added stmt_deps consist of the new existing-definition record and three landed
definition nodes. Only lean and these additions to stmt_deps change in the item node copy.

## New nodes

`def-sfb-constant-completion-coefficient-data` records the existing definitions in
`Sheaf.Paper.ConstantCompletionEquivalence` with `existing: true`; no new Lean module or
copy of a construction is introduced. Its fourteen declarations are `finite`, `completed`,
`projection`, `coefficientMap`, `Mod`, `Cx`, `D`, `Q`, `change`, `DerivedExtension`,
`derivedExtension`, `extend`, `extendComparison` and `tensorSection`, all in namespace
`CategoryTheory.ConstantCompletion`. The new node defines positive-indexed finite constant
quotients, their actual limit and its maps, the standard categories and localization,
ordinary scalar extension and its sheafification tensor insertion, and the universal
left-derived pair with its invertible K-flat comparison. Each clause is exactly the
existing declaration or the fields of `DerivedExtension`; it asserts neither flatness nor
quotient identities nor completeness. Source: Stacks sites-modules.tex section Constant
sheaves and Tag 093M, and sites-cohomology.tex Tag 06YY, specialized to the identity topos.
I read the source text and the full existing declaration signatures and docstrings.

Searches for this definition node: `msearch.py leansearch` queried "Constant ring sheaf
adic inverse limit completion with canonical projections scalar extension and universal
derived comparison" (eight ordinary AdicCompletion results); `msearch.py leanfinder`
queried "Constant coefficient ring sheaves adic completion scalar extension of sheaf
modules and derived extension of scalars comparison" (eight ordinary adic-completion
results); `msearch.py grep` queried `ConstantCompletion|DerivedExtension|extendComparison`
(zero Mathlib hits). Their actual output is recorded in the new node. Direct searches of
`dag/nodes`, `lean/WeilConjectures` and `lean/Sheaf` found the existing project constructions,
but no definition node owning these fourteen names; the only ConstantCompletion definition
nodes record kernel completeness and the separate complex-functor square. The existing
kernel-completeness node is cited, not duplicated. `tools/blueprint_refs.py search
'constant completion'` returned zero blueprint matches, and `ancestor` returned
`det-lem-integral-models-stacks`.

The new definition node assumes no Noetherian, maximality, nonemptiness or flatness
hypothesis: its objects exist also for I=0, I=A, the zero ring, an empty site and a
noncomplete coefficient ring. For I=0 the tower is constant at the constant A-sheaf;
for I=A it is the zero-ring tower. Scalar extension along an identity and along an
arbitrary ring-sheaf map uses the same existing functor and universal comparison.

## Returned delivery repair (H2)

The independent review of immutable head `83b51364a1e0` upheld one point, H2: the
constant-completion theorem node was being used for plain definitions which are not
chosen from its conclusion. I replaced that added statement dependency with
`def-sfb-constant-completion-coefficient-data`, added the already landed
`def-sfb-quotient-kernel-completeness`, and retained the theorem in proof_deps unchanged.
The former records exactly the fourteen requested declarations; the latter records
`kernelIdeal` and `IsComplete`. `derivedExtension` is chosen from the module-local
`derivedExtension_exists` helper, whose data include the universal left-derived
comparison and its K-flat computation; it is not chosen from `equivalence` or
`flat_and_quotients`. The separate normalization in the item is unchanged.

Second reading of the repair by NY: I reopened the returned item, its retained Lean
module, the kernel-completeness node and the coefficient source. The new node's
positive exponent n+1, limit projections, cone lift, standard localization,
sheafified ordinary tensor and universal comparison agree with the exact existing
definitions. Its declarations list includes all fourteen requested names. The item's
hypotheses, global and slice normalization formulas, completeness predicate, residue
cohomology and degree bounds are unchanged. The Lean file and its recorded signature
were retained verbatim. No statement correction or new postponed theorem is introduced.

Repair validation: the local self-check passed (the item changes only lean and added
stmt_deps against the current read clone, its signature matches the retained source
verbatim, both JSON files have the required layout, all fourteen existing declarations
are listed, the new node cites exactly its bracketed dependencies, and the equivalence
theorem remains only a proof dependency). No Lean source was modified during the repair.

The prescribed wrappers could not complete validation. The initial saved-packet
`deliver2.py --no-push` failed before preflight with an unknown Sheaf module prefix;
its server confirmation reported "Live published library is unavailable". After repairing
H2, I ran `scompile.py NY lem-sfb-adic-perfect-model-complete-reduction` on the retained
Lean file, then reran `deliver2.py NY lem-sfb-adic-perfect-model-complete-reduction
--no-push` on the repaired packet. Both failed on the existing dependency
`Sheaf.CategoryTheory.RingedSiteModules` with `unknown module prefix 'Mathlib'` and the
same server confirmation: "Live published library is unavailable". This is a missing
published-library/tool environment, not an item elaboration error. Nothing was pushed.
The repaired packet is retained for the next retry; no tool or published library was
modified or bypassed.

Retained Lean module SHA256: `646fb13edd21dcf1db4bdbbda56629dfcc6825684fcc5bbd42ba1723cbb418eb`.


## Retained-packet retry (2026-10-21)

As instructed, I first inspected this retained report and ran the saved packet through
`deliver2.py NY lem-sfb-adic-perfect-model-complete-reduction --no-push`. It failed before
item elaboration. A separate prescribed `scompile.py` run on the retained Lean module
failed identically. Both wrappers confirmed against current server sources and reported
"Live published library is unavailable". The concrete diagnostic is now a missing
published Mathlib object file, rather than the earlier unknown-prefix diagnostic:

`Mathlib/Algebra/Category/ModuleCat/Sheaf/Abelian.olean` does not exist under the server's
`/home/ubuntu/weil-conjectures-sheaf/lean/.lake/packages/mathlib/.lake/build/lib/lean/`.
It is required by the existing overlay `Sheaf.CategoryTheory.RingedSiteModules`, line 6.
This is a published-library/tool failure before the delivered file is checked, not an
elaboration failure that can be repaired in this packet. No library, launcher script,
or tool was modified, and no delivery was pushed.

I repeated the repair self-check against the current read clone without Git commands:
only `lean` and `stmt_deps` differ on the item; no original statement dependency was
removed; the constant-completion theorem occurs only in proof_deps; the new existing
coefficient-definition node lists exactly the fourteen requested declarations; and the
kernel-completeness node is cited. Both JSON files retain indent 1, Unicode and a final
newline. The recorded theorem signature is verbatim, all Lean lines are within 100
characters, and the retained Lean SHA256 remains
`646fb13edd21dcf1db4bdbbda56629dfcc6825684fcc5bbd42ba1723cbb418eb`.
The requested H2 repair remains complete and retained for validation when the published
library is restored.

## Retained-packet retry after second tool failure (2026-10-21)

I inspected the saved report and ran the prescribed saved-packet dry run first. It
again failed before item elaboration: the existing overlay
`Sheaf.CategoryTheory.RingedSiteModules` cannot import the missing published
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian.olean`. The wrapper's confirmation
against current server sources reports "Live published library is unavailable".
A separate prescribed `scompile.py` on the retained module returned exactly the same
missing-object diagnostic and server confirmation. Neither failure is exit 124 or
"no answer from the compile server"; both are exit 1 with the explicit missing file.

The required self-check found that the current read clone has newer maintainer-owned
`lean_audit` metadata than the retained item copy. I refreshed only that metadata from
the current node, retaining the repaired `lean` and `stmt_deps`. All other item fields
now match the current read clone exactly. The H2 repair still lists all fourteen
requested existing coefficient declarations, cites the kernel-completeness definition,
and retains the constant-completion theorem only in `proof_deps`. No original statement
dependency is removed. Both node JSON layouts and the verbatim recorded theorem
signature pass the self-check. The Lean source is unchanged, with SHA256
`646fb13edd21dcf1db4bdbbda56629dfcc6825684fcc5bbd42ba1723cbb418eb`.

I reran the prescribed dry run on this refreshed packet. The published-library failure
persists; no delivery was pushed. No shared source, launcher script, compiler setting,
or published library was modified or bypassed. The repaired packet remains in the
sandbox for validation when the published library is restored.

## Retained-packet validation retry (2026-10-21)

I first read the saved report and ran the prescribed saved-packet dry run. I then
reopened the retained Lean file, both node files, the current item node, the
kernel-completeness node and the existing ConstantCompletion declarations. Against
the current read clone, only `lean` and the four additions to `stmt_deps` differ;
no original statement dependency is removed. The equivalence theorem remains in
`proof_deps` and is absent from `stmt_deps`. The new existing-definition node is
not already present upstream and records exactly the fourteen declarations
requested by H2. `kernelIdeal` and `IsComplete` remain owned by the separately
cited `def-sfb-quotient-kernel-completeness`.

The coefficient source still defines the actual positive-indexed constant quotient
limit, its projections and cone lift, ordinary scalar extension, the standard
localizations, and the universal derived pair with its K-flat comparison. In
particular `derivedExtension` is selected from the module-local universal-pair
helper, not from the equivalence theorem or its flatness/quotient conclusion.
No Lean statement, helper or construction needed a further change. The retained
theorem signature matches `lean.statement` verbatim; both JSON files have indent 1,
Unicode and a final newline; no Lean line exceeds 100 characters. The source SHA256
remains `646fb13edd21dcf1db4bdbbda56629dfcc6825684fcc5bbd42ba1723cbb418eb`.

Validation outcome of this retry: the first dry run progressed through shared
dependency compiles, then its local overlay timed out compiling the existing
`WeilConjectures.Algebra.Homology.HomComplexSectionsCochains`. Its server
confirmation instead failed before item elaboration because the published file
`/home/ubuntu/weil-conjectures-sheaf/lean/.lake/build/lib/lean/WeilConjectures/Mathlib/LinearAlgebra/TensorProduct/Basic.olean`
is missing. The failure is reported while importing the existing
`Sheaf.CategoryTheory.RingedIdealGenerators` (line 6).

I then ran the prescribed `scompile.py NY
lem-sfb-adic-perfect-model-complete-reduction` on the retained module and repeated
`deliver2.py NY lem-sfb-adic-perfect-model-complete-reduction --no-push`.
Both failed with exit 1 on exactly this missing published object, both locally
and in their current-server confirmation. This is neither a no-answer/busy
exit 124 nor an elaboration error in the delivered file. The source module for
`WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic` exists in the read
clone; its missing published compiled artifact is outside the packet and cannot
be repaired by changing the item's statement or dependency metadata. No shared
source, launcher script, compiler limit, or published library was changed or
bypassed. No delivery was pushed. The complete H2 repair is retained for the
next validation attempt.


## Fifth retained-packet retry (2026-10-21)

I inspected the retained report and first ran the required saved-packet
`deliver2.py NY lem-sfb-adic-perfect-model-complete-reduction --no-push`.
It failed with exit 1 before checking the item: the existing overlay
`Sheaf.CategoryTheory.RingedIdealGenerators` imports the missing published
`WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic.olean`. Current-server
confirmation reproduced exactly that missing-object error. A separate prescribed
`scompile.py` on the retained module also failed with exit 1 on that object
(local overlay `RingedSectionLocalization`; server confirmation
`ExtendedCechReflectorCore`). Neither result was a busy-server exit 124.

I checked the saved H2 repair against the current read clone without Git commands.
The item differs only in `lean` and the four permitted additions to `stmt_deps`;
no original statement dependency is removed. The constant-completion theorem is
only a proof dependency. The new existing-definition node is still absent upstream,
lists exactly the fourteen requested declarations, and is cited alongside the
existing kernel-completeness node. The new node's bracket citations equal its
statement dependencies. Both JSON layouts, the verbatim recorded theorem signature
and the 100-character Lean line limit pass. No repair handoff file is present.
The Lean source remains unchanged, SHA256
`646fb13edd21dcf1db4bdbbda56629dfcc6825684fcc5bbd42ba1723cbb418eb`.

The published compiled object is outside the packet. The prescribed wrappers fail
before item elaboration, so the missing artifact cannot be repaired by an item
statement or metadata edit. No shared file, published artifact or launcher tool was
modified or bypassed. The H2 repair is retained; nothing was pushed.

## Current retained-packet self-check (2026-10-21)

I reopened the retained Lean module, both packet nodes, the current base item and
kernel-completeness node, and the existing ConstantCompletion definitions. H2 is
repaired exactly as requested: the new existing-definition node lists `finite`,
`completed`, `projection`, `coefficientMap`, `Mod`, `Cx`, `D`, `Q`, `change`,
`DerivedExtension`, `derivedExtension`, `extend`, `extendComparison`, and
`tensorSection`; the separate kernel-completeness node supplies `kernelIdeal`
and `IsComplete`. The equivalence theorem remains in `proof_deps` only.
`derivedExtension` still selects the universal pair from its module-local
existence helper, not from `equivalence` or `flat_and_quotients`.

Against the current base, the item changes only `lean` and the four permitted
statement-dependency additions, with no original dependency removed. The new
node is absent from the base. The theorem signature remains verbatim, both JSON
files retain the required layout, and every Lean line is at most 100 characters.
There is no repair handoff note. The Lean source is unchanged, with SHA256
`646fb13edd21dcf1db4bdbbda56629dfcc6825684fcc5bbd42ba1723cbb418eb`.

Current validation succeeded: `deliver2.py NY
lem-sfb-adic-perfect-model-complete-reduction --no-push` reported
`OK (dry run): commit 6923ebc3ca0 passes the preflight and compiles; nothing pushed`.
The server compiled the item and the existing-declaration probe cleanly under the
standard per-file limit. The previously missing published tensor-product artifact
no longer blocks this packet. The retained H2 repair is ready for delivery; no
shared source, published artifact, launcher tool or compiler setting was edited.
