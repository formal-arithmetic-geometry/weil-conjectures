## Worker report

The module `Sheaf.AlgebraicGeometry.ClassicalModuleWeakSerre` states
`AlgebraicGeometry.ProEtale.classicalModule_weakSerre`. Its only proof is `sorry`.
The statement is unchanged from the node and the current blueprint detail file
`sec-proetale-coefficients/sk-cor-pe-classical-derived/`
`sk-cor-pe-classical-derived-weak-serre.md`. No new notion is defined.

Hypotheses and clauses, individually:

- An arbitrary scheme is `(X : Scheme.{u})`; no separation, quasi-compactness,
  affineness or nonemptiness hypothesis is imposed.
- An arbitrary discrete commutative ring is `(Λ : Type u) [CommRing Λ]`.
  No topology or finiteness hypothesis is supplied. Both objects can be placed
  in a common universe; the inherited module category uses coefficients
  `ULift.{u+1,u} Λ` and modules of size `u+1`, exactly as the dependency.
- The objects are the intrinsic sheaves of modules over the constant ring sheaf
  on `Scheme.ProEt.topology X`, through the domain of
  `IsClassicalModule (X := X) Λ`. That predicate uses the actual linear
  `moduleContinuityMap` for every affine etale presentation; it is not replaced
  by an assumed essential-image predicate or by arbitrary value-category sheaves.
- Containment of zero is literally `IsClassicalModule (X := X) Λ 0`.
  The standard Mathlib `ZeroObject` scope supplies the categorical zero object.
- Kernel closure is `ObjectProperty.IsClosedUnderKernels
  (IsClassicalModule (X := X) Λ)`. Reading its definition in
  `Mathlib.CategoryTheory.ObjectProperty.Kernels`: it requires classicality of
  the vertex of every limiting kernel fork of every morphism whose two objects
  are classical. In particular it gives classicality of `kernel f`.
- Cokernel closure is `ObjectProperty.IsClosedUnderCokernels` of the same
  predicate; dually it covers every colimiting cokernel cofork, hence `cokernel f`.
- Extension closure is `ObjectProperty.IsClosedUnderExtensions` of that
  predicate. Its defining field quantifies over `S : ShortComplex C`, assumes
  `S.ShortExact`, classicality of `S.X₁` and `S.X₃`, and concludes classicality
  of `S.X₂`. Thus these are exactly the displayed short exact sequences.
- The full subcategory is the full subcategory of this object predicate; the
  theorem asserts its four specified closure properties. It does not assert
  the stronger Serre condition of closure under arbitrary subobjects/quotients.

The kernel/cokernel classes quantify over all universal presentations rather
than one chosen representative. This is equivalent to the node's formulation:
`isClassicalModule_iff` and `isClassical_iso_iff` in the dependency show that
module classicality is invariant under isomorphism. No extra closure assumption
is imposed. The extension class already matches the node verbatim.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ClassicalContinuityMap`:
  `AlgebraicGeometry.ProEtale.IsClassicalModule`, with
  `moduleSectionPresheaf`, `moduleContinuityMap`, `AffinePresentation`,
  `IsClassical`, `IsClassicalCochainComplex` and the underlying-set comparison.
  Read the full published source as well as the local source and the definition
  unit. The definition node `sk-def-pe-classical-definition` has no Lean record;
  its `same_as` detail node already owns these exact definitions. This delivery
  attaches them to that dependency as existing declarations; see below.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, the transparent Mathlib
  `SheafOfModules` abbreviation used by the preceding signatures.
- The public Mathlib imports provide exactly the kernel, cokernel and extension
  closure classes described above. All variables and universes are explicit;
  `set_option autoImplicit false` is also set in the file.

Proof dependencies are imported non-publicly for stage 3: the ringed-site
Grothendieck theorem, enough injectives, small-site comparison, the module-sheaf
category, the single-object right-derived identification, derived category,
full long exact sequence, degree-zero right-derived identification and short
five lemma. `def-weil-size-convention` is metatheoretic and has no module.
`det-pe-classical-sheaves-modules` has no recorded declaration or module, so its
import cannot yet be added. The seven-step proof docstring follows the node:
exact full faithfulness gives zero and kernels/cokernels; the derived unit and
single-object comparison give R¹-vanishing; the long exact sequence and counit
short-five-lemma diagram give extension closure.

The recorded comparison proof module
`Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison` failed import through
the prescribed compiler: its old `Derived.LowerShriek` import redeclares
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification`, already
provided by the published `FiniteCoefficient.Derived.LowerShriek` module.
Following the launcher's instruction to use the smaller upstream module, the
file imports `WeilConjectures.SixFunctors.ProEtale.Derived.Comparison` instead.
Its existing `isIso_derivedComparisonAdjunction_unit_app`, whose full signature
and docstring were read, supplies precisely the bounded-below derived unit
used in steps 4--5. The broken larger proof import is deferred; no live file or
proof-dependency node is edited and the statement is unaffected.

Edge cases checked before writing: the empty scheme, the zero coefficient ring,
the zero morphism between classical objects, an identity morphism (zero kernel
and cokernel), a short exact sequence with either endpoint zero, and arbitrary
cofiltered presentation categories including parallel arrows. No nonzero-ring,
nonempty-scheme or finite-index restriction is present. Cofilteredness in the
existing predicate already includes nonemptiness; no new condition is added.

Searches made on 2026-10-17:

- `msearch.py leanfinder`, query "Classical sheaves of modules on the pro etale
  site are closed under kernels cokernels and extensions": eight hits on
  abelian module-sheaf categories, condensed modules and quasicoherence; no match.
- `msearch.py leansearch`, query "Classical module sheaves on a scheme pro
  etale site contain zero and are closed under kernels cokernels and extensions":
  eight hits on generic sheaf abelian categories and sheafification; no match.
- `msearch.py loogle`, query
  `CategoryTheory.ObjectProperty.IsClosedUnderExtensions,
  CategoryTheory.ObjectProperty.IsSerreClass`: the Serre-class constructor and
  its extension-closure projection; neither establishes this weak Serre result.
- `msearch.py grep`, query `WeakSerre|weakSerre|IsClassicalModule`, restricted
  to Mathlib `CategoryTheory`: zero hits.
- `rg` in Mathlib's `ObjectProperty` sources found and fully inspected
  `ContainsZero`, `IsClosedUnderKernels`, `IsClosedUnderCokernels` and
  `IsClosedUnderExtensions`. These are generic notions, not this theorem.
- `rg` for `IsClassical|isClassical|classical.*(Module|[Ss]heaf)|[Ww]eakSerre`
  in the source project and `lean/Sheaf` located the existing continuity
  predicates and generic weak-Serre cohomology results. No theorem of this
  classical-module closure exists. The direct item-id source search returned
  no hit, and the proposed declaration name has no existing match.
- The dependency node explicitly lists the detailed continuity node in
  `blueprint.same_as`; its existing module defines all three clauses of the
  definition unit, so no additional definition node or copied definition is needed.

There is no statement dispute or statement correction.

## Dependency modules

`sk-def-pe-classical-definition`: no new module is needed. The node had no
recorded declaration, although its `same_as` detail node
`det-pe-classical-definition-continuity-map` already supplies its entire notion
in `Sheaf.AlgebraicGeometry.ClassicalContinuityMap`. This is an existing-record
repair under §1(B): only `lean` is added, with `existing: true` and a note.
The primary declaration is `AlgebraicGeometry.ProEtale.IsClassical`, and the
record also lists `IsClassicalModule` and `IsClassicalCochainComplex` so that
the module and every-cohomology-sheaf clauses are explicit. Their sources and
full signatures were read. The set predicate requires bijective continuity
maps; the module predicate requires invertible linear continuity maps for
the same presentations; the cochain predicate quantifies over every integer
cohomology sheaf. These are exactly the definition node and its source unit.
Its statement, dependency list and all other fields are unchanged.


## Second reading by Q121

I independently read the item node, its seven proof steps, its sandbox module,
the current source statement and proof in
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/`
`sk-cor-pe-classical-derived/`, and the parent unit `_section.md`.
The item's source is this blueprint detail, rather than a Stacks tag. I also
read `sk-def-pe-classical-definition/_section.md` and the continuity-map detail,
which supply the subsection-wide discrete commutative coefficient convention.
There is no additional separatedness, Noetherian, quasi-compactness, nonzero,
or characteristic hypothesis in these source passages. No maintenance repair
note exists for this item, and there is no `statement_change` to audit.

My object/hypothesis/conclusion checklist, with the Lean file open:

1. **A scheme X.** `(X : Scheme.{u})` introduces precisely an arbitrary scheme.
   There is no additional instance on X. Verdict: matches.
2. **A discrete commutative coefficient ring.** `(Λ : Type u) [CommRing Λ]`
   introduces precisely the ring; the constant-sheaf construction supplies
   discrete coefficients, so no topology instance is wanted. No field,
   finite-ring, Noetherian or characteristic condition appears. Verdict: matches.
3. **The category Mod(X_Proet, Λ_X).** I opened the recorded dependency module
   `Sheaf.AlgebraicGeometry.ClassicalContinuityMap`, not just its declaration
   names. Its `IsClassicalModule` takes an intrinsic
   `ringedSiteModules.{u + 1}` over the constant CommRingCat sheaf of
   `ULift.{u + 1, u} Λ`, forgotten to RingCat. I opened
   `Sheaf.CategoryTheory.RingedSiteModules`: this is transparently the existing
   Mathlib `SheafOfModules`, whose objects and sectionwise linear morphisms I
   checked in `Mathlib/Algebra/Category/ModuleCat/Sheaf.lean`. The site's
   `Scheme.ProEt` and `Scheme.ProEt.topology` are the small weakly-etale site
   with its recorded covering topology, as read in Mathlib's Sites/Proetale
   and the imported project Proetale/Basic. Verdict: the correct category.
4. **The full subcategory of classical objects.** The object predicate is
   exactly `IsClassicalModule (X := X) Λ` from that dependency. I traced its
   body to `IsIso (moduleContinuityMap Λ F P)` for every `AffinePresentation`.
   Such a presentation has cofiltered affine etale stages over X, an affine
   cone vertex, and the scheme-limit universal property. The map is the actual
   `colimit.desc` of restriction along the projection cone, after restriction
   of section scalars along the constant-section sheafification unit. Thus
   classicality means the source's linear continuity isomorphism, without a
   substitute essential-image hypothesis. A full subcategory is determined by
   this object predicate; no separate categorical structure is asserted.
   Verdict: matches the source and dependency node.
5. **Contains zero.** `IsClassicalModule (X := X) Λ 0` is the first conjunct.
   The `ZeroObject` scope selects the categorical zero object of this module
   category. Verdict: matches.
6. **Kernels of every map of classical objects.** The second conjunct is
   `ObjectProperty.IsClosedUnderKernels (IsClassicalModule (X := X) Λ)`.
   I read `MorphismProperty.kernels`, `ofObjectProperty`, and the closure
   class: it quantifies over every morphism with both endpoints classical
   and every limiting kernel fork. Its `prop_kernel` gives the node's chosen
   kernel. Verdict: matches. Quantifying over all universal representatives
   changes no mathematical condition, since module classicality is invariant
   under isomorphism by `isClassicalModule_iff` and `isClassical_iso_iff`.
7. **Cokernels of every such map.** The third conjunct is the corresponding
   `ObjectProperty.IsClosedUnderCokernels`. I checked the dual colimiting
   cofork definition and `prop_cokernel`. Both endpoint hypotheses and the
   order of universal quantification match. Verdict: matches, with the same
   isomorphism-invariance observation.
8. **Extensions.** The final conjunct is
   `ObjectProperty.IsClosedUnderExtensions (IsClassicalModule (X := X) Λ)`.
   I read its field `prop_X₂_of_shortExact`: for any short complex S it assumes
   `S.ShortExact`, classicality of S.X₁ and S.X₃, and concludes classicality
   of S.X₂. These are exactly G', G and E in the displayed sequence of the
   node. It imposes no condition on the middle term in advance. Verdict: matches.

Edge cases: X may be empty; Λ may be the zero ring or have any characteristic;
the objects and maps may be zero. Identity maps are included, so their zero
kernels and cokernels are included. Extensions with a zero endpoint are
included. No natural-number parameter or degree bound occurs in the statement;
the degree-one calculation is only the proof's extension argument. Empty index
categories are excluded only by the dependency's cofilteredness, as required
for the affine presentations; singleton presentations and categories with
parallel arrows are allowed. I checked the index and value sizes in that
module: both are u+1, while the underlying schemes and Λ are in u. This is the
recorded common-larger-universe convention. Scheme and coefficient data of
different initial sizes can be placed in a common containing universe; the
statement imposes no equality between distinct site object and morphism
universes, and retains the dependency's exact size interface.

Independent duplicate searches (2026-10-17):

- `msearch.py ... leanfinder`: “The essential image of pullback from etale
  sheaves to proetale sheaves is stable under exact extensions and kernels”.
  Eight hits: condensed exact-(co)limit infrastructure, locally constant
  condensed essential-image characterizations, coherent sheaf comparison and
  the etale topology. None states this classical-module weak Serre theorem.
- `msearch.py ... leansearch`: “Classical proetale module sheaves form a weak
  Serre subcategory”. Eight hits: generic Serre-class constructors/projections
  and SheafOfModules recursors. None establishes the requested class's closure.
- `msearch.py ... loogle` with both
  `CategoryTheory.ObjectProperty.IsClosedUnderKernels` and
  `CategoryTheory.ObjectProperty.IsClosedUnderExtensions`: zero hits.
- `rg` throughout pinned Mathlib for weak Serre, ClassicalModule, classical
  pro-etale, or essential-image extension-closure terms: no exact match.
  Broader kernel/cokernel/extension searches located the generic closure
  classes, which I read in full in ObjectProperty/Kernels and Extensions.
- `rg` in the source project's WeilConjectures, the shared `lean/Sheaf`, and
  the upstream pro-etale framework: the continuity predicate is already
  defined, and the generic homology-property theorem assumes weak Serre
  closure. I opened `HomologyProperty.lean`,
  `FiniteTypeLocallyConstantSerre.lean` and `SfFullcdUsedClass.lean`: they concern
  respectively an arbitrary already-closed class, finite-type locally
  constant sheaves over a Noetherian ring, and particular finite coefficient
  rings on finite-type schemes. None has this theorem's objects and generality.
  The upstream name table and pro-etale source searches found no collision
  with `classicalModule_weakSerre`.

No missing notion, new definition node, new dependency module or hollow
construction is needed. The sole theorem has `sorry` as its entire proof.
The module and theorem docstrings name the exact source and blueprint id, and
its seven numbered proof steps cover all seven DAG steps: exact fully faithful
comparison, kernel/cokernel transport, enough injectives and left exactness,
derived unit on a single object, degree-one vanishing, the long exact sequence,
and the counit diagram plus short five lemma. The proof-only imports are
non-public. I read the upstream derived comparison theorem's full ambient
hypotheses and signature; for ModuleCat coefficients it supplies the stated
bounded-below derived unit. The larger recorded comparison module's import
collision remains documented in the worker report; this delivery uses its
smaller upstream comparison input. I also read the current Grothendieck and
long-exact-sequence modules through `scompile.py --source`, and the recorded
single-object, degree-zero and short-five-lemma interfaces.

**Mismatch repaired:** the worker's dependency-node copy would overwrite the
already-landed `sk-def-pe-classical-definition` existing binding from Q18 with
an equivalent Q121 record. I checked the published binding against all three
actual definitions (sets, modules, and every integer cohomology sheaf); it is
already exact. I removed that stale sandbox node copy. The dependency section
of the worker report describes its original proposal; no dependency-node
change is now delivered. The item and Lean signature require no correction,
and only the item's `lean` field differs from the current shared node.

Validation: the prescribed `scompile.py` compiled the sole delivered module
as both sandbox and library file in 1.8 s and 2.0 s, with no diagnostics.
`autoImplicit false` and `universe u` leave no unbound variable or universe.
The node's `lean.statement` equals the source signature verbatim; every Lean
line is at most 100 characters. No statement hypothesis or conclusion changed.
