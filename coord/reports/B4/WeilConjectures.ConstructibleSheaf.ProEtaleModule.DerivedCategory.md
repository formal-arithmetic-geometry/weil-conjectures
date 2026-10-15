## What changed

Repaired `lean/WeilConjectures/ConstructibleSheaf/ProEtaleModule/DerivedCategory.lean`.
The original `AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible` is false for
arbitrary ring objects; the replacement makes kernel, cokernel and extension closure
explicit hypotheses and proves the triangulated structure from them. No definition or
target statement changed. This is a statement repair, not a proof of the original claim.

The proof establishes isomorphism invariance by transporting each local presentation and
constructibility of zero by the rank-zero identity presentation, identity cover, and
one-stratum stratification. It applies the already proved general weak Serre theorem
`DerivedCategory.homologyProperty_isTriangulated` and intersects with the bounded part of
the canonical t-structure. The three new helpers are private and fully proved.

The only new proof import is
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty`, privately.
Two public Mathlib imports provide the closure classes appearing in the new signature:
`Mathlib.CategoryTheory.ObjectProperty.Kernels` and
`Mathlib.CategoryTheory.ObjectProperty.Extensions`.

Validation: the corrected module compiles without warnings in about three seconds.
`#print axioms AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible` reports
exactly `propext`, `Classical.choice`, and `Quot.sound`. All three direct importers compile
unchanged against the corrected module: `Sheaf.Paper.CondensedSheafExtContinuity`,
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`, and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
The check used individual-file compilations through `lcompile.py`, with a sandbox overlay.
No forced adaptations are needed or delivered. The change record lists all 37 downstream
modules and their current holders.

## Proved and sorry left

Original module: one hole, in
`AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible`.
The original noetherian-only statement is **not proved**: it is false. It has been
corrected, and the corrected declaration is fully proved, with node
`prop-weil-pbc-module-bounded-constructible-triangulated`.
This closes one textual hole by a justified statement repair, not by proving an
unchanged statement. No new holes, no decomposition, and no `sorry` remain in the delivery.

Proved private helpers: `constructible_of_iso`,
`locallyFinitelyPresented_of_isZero`, and `constructible_of_isZero`.

## No longer needed

No existing import or dependency module is removed. The original instance had neither a
proof plan nor a theorem node attached to it. The unrestricted assertion that topological
noetherianity alone supplies coefficient-module kernel closure is removed as false.
No generic closure theorem is split off or imported. The field-specific
`Sheaf.AlgebraicGeometry.CondensedConstructibleSerre` is not imported: it cannot prove
closure for an arbitrary ring object and would introduce an import cycle.

The proof uses the closed general homology-property declaration recorded under
`prop-constructible-derived-subcategory` as a tool. It does not import that node's
specialized etale constructibility module or its extra proof dependencies. No blueprint
unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the original instance's noetherian-only signature is false. Let
`B = k ⊕ V` with `V` an infinite-dimensional vector space and square-zero multiplication.
For nonzero `e ∈ V`, multiplication by `(0,e)` on `B` has kernel `V`, which cannot be
finitely generated as a `B`-module because the action factors through `k`.
The source and target are rank-one free. Constant discrete sheaves over a geometric point
realize this example. Any local finite presentation of the kernel would give a finite
presentation on its geometric fiber, a contradiction. The cone of the corresponding map
of degree-zero bounded constructible complexes has this nonconstructible cohomology.
The base is a one-point noetherian scheme. The full calculation and the precise old/new
signatures are in the change record.

The old module docstring treated the three closure facts as unproved consequences of
noetherianity, without a coefficient condition. That assertion has been corrected.
The existing field-specific Serre node is narrower and supplies no justification for the
arbitrary-ring assertion. A false generic Serre lemma has not been added to make the
original statement appear proved.

The category-definition node `def-weil-pbc-condensed-e-module-category` records
`boundedConstructible` and `BoundedConstructible` among its audited declarations; its main
`lean` attachment is now the continuous-coefficient universe interface. Other DAG hits
mention this module in sources or search records, but none attaches the former instance
or supplies a proof plan for it. The category definitions remain unchanged. A new node records the conditional structural
API; it is marked unreachable because no higher declaration currently uses this instance,
although the module itself is imported for its category definitions.

## New nodes

`prop-weil-pbc-module-bounded-constructible-triangulated`, in
`dag/nodes/sec-proper-base-change/`, records the corrected conditional instance, its
zero/isomorphism proofs, and use of the existing general weak Serre construction.
Its Mathlib searches were run with Lean Finder, Loogle, grep, and LeanSearch; LeanSearch
returned an internal server error and is recorded as unavailable. Searching the whole
blueprint found the generic weak Serre argument under
`prop-constructible-derived-subcategory`, which is used as a proved tool rather than
repeated. The new node adds no unresolved theorem.

Change record: `coord/changes/proetale-module-constructible-triangulated.md`.

## Second reading by B4

1. **Interfaces and statement repair: PASS as a declared correction.** I compared the
   complete delivered module with the repository using `diff` and the delivery parser.
   The signatures, bodies and docstrings of `boundedConstructible`,
   `mem_boundedConstructible_iff` and `BoundedConstructible` are unchanged. The sole
   existing signature change is `isTriangulated_boundedConstructible`, recorded in
   `coord/changes/proetale-module-constructible-triangulated.md`: topological
   noetherianity is replaced by kernel, cokernel and extension closure. This is not a
   proof of the old statement. I checked the square-zero example explicitly:
   `(a,v)(0,e) = (0,ae)`, so its kernel is the infinite-dimensional square-zero ideal,
   on which scalar multiplication factors through the field. It is not finitely
   generated. Taking constant discrete sheaves with `A = Ab` over a geometric point
   realizes the example; a local finite free presentation would induce one on the
   geometric fiber, which is impossible. The cone has this kernel as cohomology.
   Stacks 05CU, Definition 10.90.1 and Lemmas 10.90.3–4, confirm the coefficient coherence
   distinction, rather than a consequence of noetherianity of the base space.
   I reran the downstream query: 37 downstream modules, no code reference to the old
   instance outside its defining module. The three direct importers were copied from
   the repository unchanged and compiled individually in import order against a fresh
   sandbox overlay of the repair. No consumer adaptation or target change is delivered.

2. **Proof and trust: PASS.** The delivered file compiles cleanly with `lcompile.py`.
   In a scratch copy I ran `#print axioms` on the instance and each private helper;
   all four use exactly `propext`, `Classical.choice` and `Quot.sound`, without
   `sorryAx`. There are no remaining holes, forbidden declarations or hollow
   definitions. The isomorphism proof composes the inverse of the restricted module
   isomorphism with the given presentation, with the correct orientation. The zero
   proof uses a rank-zero identity presentation and preservation of zero by the
   restriction functors. The final `change` identifies exactly the intersection of
   boundedness with the existing homology property; the existing weak Serre instance
   and the intersection instance finish the proof. No object is chosen from an
   unproved existence theorem.

3. **Split statements and small cases: PASS.** No statement with `sorry` is split off,
   and no new unresolved node is added. The new node records the corrected proved
   instance, not a restatement used to hide an unchanged hole. Its three closure
   hypotheses are precisely the hypotheses used by the generic weak Serre theorem.
   I checked the zero object, rank-zero presentation, empty scheme and empty strata:
   the identity cover and single (possibly empty) stratum work without noetherianity
   or any nonemptiness assumption. The construction also works for a zero ring.
   Searches for `IsConstructibleModuleObject`, `IsLocallyFinitelyPresented` and
   `homologyProperty_isTriangulated` across both Lean roots found no existing generic
   pro-etale module zero/isomorphism lemmas. Independent Lean Finder, Loogle and grep
   searches using weak Serre closure and triangulated-object-property terminology
   found no shorter Mathlib specialization. The already proved upstream general
   theorem is used directly.

4. **Route and pruning: PASS.** I read
   `lean/WeilConjectures/Mathlib/Algebra/Homology/DerivedCategory/HomologyProperty.lean`, its generic weak Serre proof, the attachment
   under `prop-constructible-derived-subcategory`, and
   `dag/units/sk-thm-properbasechange.json`. The latter's realized statement and all
   three realized steps are unchanged. The old instance had no attached proof plan,
   so there are no old `proof_deps` to retire. No original import or module is pruned.
   The new homology-property import is private and serves only the proof; the two new
   public Mathlib imports expose the classes in the corrected signature. A scratch
   probe with the original public imports confirmed all three classes were absent,
   so these imports are needed for the public interface. The existing
   `Scheme.Stratification.trivial` is in the unrelated small-etale open/closed module
   and unavailable under these imports; constructing a local one-stratum witness
   adds no duplicate public definition or extra import dependency. The field-specific
   Serre theorem cannot prove the original arbitrary-ring assertion and is not used.

5. **DAG and report: PASS.** The new node's three proof steps match the private
   isomorphism argument, the zero argument, and the application of the generic
   homology-property instance followed by bounded intersection. Its sole `proof_deps`
   entry records that existing theorem's node; `proof_origin` names this proof.
   The source, chapter, unit, creation fields, blueprint ancestry, search records and
   Lean declaration are present. The node has no unresolved proof obligation. Its
   note distinguishes the unchanged category definitions from the corrected
   structural instance, and its unreachable flag refers to the instance, not the
   imported category definitions. The report correctly counts the old false statement
   as unproved: zero unchanged holes proved, one false statement repaired with a
   proved replacement, zero holes added, zero split off.

**Changes made in the second reading:** corrected the report's overly broad claim that
there was only one DAG search hit mentioning this module: other nodes cite it as a source,
while no node attaches the former instance. Added this independent review and its
validation evidence. The Lean proof, signatures and node required no further repair.
