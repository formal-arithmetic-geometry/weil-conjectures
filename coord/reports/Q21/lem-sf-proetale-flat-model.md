## Worker report

The node is already stated by the published upstream framework declaration
`AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn_iff_exists_flatModel` in
`WeilConjectures/SixFunctors/ProEtale/Derived/FlatModel.lean`; no duplicate module is
written. The declaration has the following signature:

```lean
theorem torAmplitudeIn_iff_exists_flatModel (a b : ℤ) (_hab : a ≤ b)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (_hK : DerivedCategory.boundedConstructible A X K) :
    torAmplitudeIn A X a b K ↔
      ∃ P : CochainComplex (Sheaf (Scheme.ProEt.topology X) A) ℤ,
        ((∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q)) ∧
          ∀ q : ℤ, ObjectProperty.flat (P.X q)) ∧
          Nonempty (K ≅ (_root_.DerivedCategory.Q).obj P)
```

(The source uses `Scheme.ProEt.topology`; the abbreviated display above is recorded
verbatim in the node's `lean.statement` field as `Scheme.ProEt.topology`.) The explicit
`_hab : a ≤ b` is the interval-order hypothesis. The `_hK` binder is bounded
constructibility. The left side is the recorded pro-etale Tor-amplitude predicate. The
right side introduces a cochain complex `P`, requires every degree outside `[a,b]` to be
zero, requires every term to be flat, and supplies a nonempty derived-category
isomorphism from `K` to `Q.obj P`.

Dependency declarations consulted:

- `def-weil-finite-tor-amplitude`: the finite Tor-amplitude definition node; its DAG
  declaration is not needed because this theorem states the interval predicate directly.
- `def-weil-finite-torsion-constructibility`: `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`
  in `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`.
- `def-weil-pbc-proetale-site`: `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`
  in `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`.
- `lem-exc-constant-inverse-image-flat`:
  `AlgebraicGeometry.ProEtale.flat_comparisonUpperStar_obj` from the upstream framework.

Searches found no Mathlib declaration for this theorem (`msearch.py leanfinder`, query
“pro etale tor amplitude iff exists bounded flat complex”; `msearch.py loogle`, query
`torAmplitudeIn`; grep of Mathlib for `torAmplitudeIn_iff_exists_flatModel`). A search of
`WeilConjectures/` found the exact upstream declaration in
`SixFunctors/ProEtale/Derived/FlatModel.lean`. `scompile.py` with a check file importing
that module and printing the declaration completed cleanly.

Edge cases checked: `a = b` is allowed; the outside-interval condition then applies to
all other integer degrees. Empty/zero complexes are handled by the explicit `IsZero`
condition, and no extra nonemptiness or coefficient assumptions are introduced beyond
the declaration's category instances.

## Second reading by Q21

I opened the node, the complete source theorem (including the ambient variables before
its namespace), both definitions it actually uses, the recorded dependency modules,
and the sole direct citer. The original Worker report above is retained as the first
reader's report; its assertions of an exact arbitrary-ring/intrinsic-constructibility
match are superseded by this reading and the correction below.

The original node's inventory and the item-by-item comparison were:

1. A commutative coefficient ring A. MISMATCH: the source parameter
   `(A : Type u')` has `[Category.{u + 1} A]`, `[Abelian A]`,
   `[IsGrothendieckAbelian.{u + 1} A]`, `[MonoidalCategory A]`,
   `[MonoidalPreadditive A]`, `[SymmetricCategory A]`, `[MonoidalClosed A]`,
   and `[Abelian.HasFunctorialFlatResolution A]`. A denotes a CATEGORY.
   The source also has `{FA}`, `{CA}`, `FunLike`, and `ConcreteCategory`
   binders specifying its concrete structure, with underlying sets in `Type (u+1)`.
   The Worker report omitted these hypotheses and asserted their applicability to
   arbitrary rings without checking a specialization. Corrected the internal node to
   the exact categorical source statement, with all these structures explicit.
2. A scheme X and its SMALL pro-etale site. MATCH for the site: `{X : Scheme.{u}}`
   and `Scheme.ProEt.topology X`. MISMATCH for the sheaf CATEGORY: source objects
   are `Sheaf (Scheme.ProEt.topology X) A`, not the recorded
   `Scheme.proEtaleDerivedCategory X R`, which uses modules over a constant ring
   sheaf (with an explicit ULift). These are not definitionally identical encodings.
   The corrected node explicitly uses A-valued sheaves and the abstract derived
   category, rather than silently identifying the encodings.
3. Integers a and b with a <= b. MATCH: `(a b : ℤ) (_hab : a ≤ b)`.
   The correction retains the ordered-interval hypothesis verbatim.
4. An object K in that derived category. MATCH after the category correction:
   `(K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))`.
5. Bounded constructibility, originally cited through
   `def-weil-finite-torsion-constructibility`. MISMATCH: the dependency's recorded
   `Scheme.intrinsicFiniteTorsionConstructible` has parameters l, E, n >= 1 and uses
   the fixed ring `Padic.coefficientExtensionRing l E n`. Its body requires finite
   cohomological support and intrinsic constructibility of all cohomology sheaves.
   In contrast, source `_hK : DerivedCategory.boundedConstructible A X K` is
   `(Etale.DerivedCategory.boundedConstructible A X).map
   (ProEtale.comparisonUpperStar A X).mapDerivedCategory`.
   `Constructible.lean`, implementation notes and declaration docstring, explicitly
   warns that this etale-origin reading must not be identified with the intrinsic
   predicate for arbitrary coefficients. The new definition record
   `def-sf-categorical-proetale-constructibility` reuses this exact existing predicate.
6. Tor amplitude in [a,b]. The ORIGINAL dependency `def-weil-finite-tor-amplitude`
   is a finite/integral/rational coefficient construction, with no usable Lean record
   for the generic categorical interval property. Its underlying interval node
   `def-weil-proetale-tor-amplitude` records
   `Scheme.HasProEtaleTorAmplitude`, using the constant-ring SheafOfModules encoding
   and all K-flat representatives. The source instead uses
   `ProEtale.DerivedCategory.torAmplitudeIn A X a b K`, an abbreviation of
   `_root_.DerivedCategory.torAmplitudeIn` on its A-valued sheaf category.
   Its body quantifies over EVERY sheaf in degree zero, with no flatness or
   constructibility assumption on the test sheaf. The new definition record
   `def-sf-categorical-proetale-tor-amplitude` reuses this precise existing predicate.
7. Existential cochain complex P of the same sheaves. MATCH:
   `∃ P : CochainComplex (Sheaf (Scheme.ProEt.topology X) A) ℤ`.
   It occurs after K and the equivalence, so one P represents the whole K.
8. Every term flat. MATCH: `∀ q : ℤ, ObjectProperty.flat (P.X q)`.
   I printed `ObjectProperty.flat`: it means exactness of BOTH tensorLeft and
   tensorRight. In this symmetric closed abelian setting, tensor is right exact,
   so this agrees with the corrected node's preservation-of-monomorphisms clause.
   No termwise constructibility, finite generation, or projectivity is concluded.
9. Every term outside [a,b] zero. MATCH:
   `∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q)`.
   This is actual termwise vanishing up to zero object, not only cohomology vanishing.
10. K is isomorphic to the derived image of P. MATCH:
    `Nonempty (K ≅ (_root_.DerivedCategory.Q).obj P)`.
    Nonempty here asserts the EXISTENCE OF AN ISOMORPHISM, not an arbitrary map or
    an arbitrary chosen model. The converse and forward implications are both present.

I then reread the corrected node against the source FIRST. Its hypotheses now list
exactly the structures above; its bounded-constructibility and Tor-amplitude predicates
are exactly the existing source definitions; and conclusions 7-10 are unchanged.
No field/ring restriction, Noetherianity, characteristic assumption, finite-coefficient
restriction, or extra nonemptiness hypothesis has been introduced. This is an explicit
source-interface correction under brief-stage2 section 1(C), not a weakening to make
an unproved theorem easier. The source theorem is already proved.

The corrected node's dependency signatures were also checked: `Scheme.ProEt` and
`ProEt.topology` give the site with scheme universe u, object universe u+1 and morphism
universe u; `DerivedCategory` gives the localization; and `IsGrothendieckAbelian`
is the existing generic Mathlib class recorded by its Mathlib-leaf node. The two new
nodes supply the precise source coefficient predicates, not new Lean implementations.
The original `flat_comparisonUpperStar_obj` signature was read in
`WeilConjectures.SixFunctors.ProEtale.Comparison.Flat`; it is about the comparison
inverse image, and is not a hypothesis or dependency of the general flat-model source
proof. It was removed from this corrected attachment's statement dependencies.

Edge cases: a=b, including a=b=0, is covered; arbitrary negative endpoints are covered.
The zero complex and zero object are allowed. There is no index set to assume nonempty;
finite stratifications in the source permit zero strata on the empty scheme.
`X : Scheme.{u}` is arbitrary, including the empty scheme. No characteristic or n
parameter belongs to the corrected source theorem. The independent u' of the
coefficient category is retained; only its morphism and underlying-set universes are
u+1, exactly as printed by the compiler. There is no imposed equality between the
site's object and morphism universes. All inherited binders were checked by `#print @`
output/the full elaborated theorem; none are left unbound.

Independent searches (using different wording from the first worker):

- msearch.py LeanFinder: "bounded resolution by flat sheaves and vanishing derived
  tensor outside an interval" returned derived-category support and projective Tor
  vanishing lemmas, not this equivalence.
- msearch.py LeanSearch: "A complex of sheaves has Tor amplitude in an integer interval
  if and only if it is isomorphic to a bounded complex of flat sheaves" was unavailable
  (Internal Server Error). No absence claim is based on this failure.
- msearch.py grep: `flat.*model|model.*flat|torAmplitudeIn_iff` under Algebra/Homology:
  no Mathlib match.
- msearch.py LeanSearch on the etale-origin essential-image definition was also
  unavailable; LeanFinder on "bounded constructible objects of etale origin in derived
  category of pro-etale sheaves" returned only site definitions. msearch.py grep for
  `boundedConstructible|torAmplitudeIn|plusEtaleOrigin` found no Mathlib matches.
- Direct rg of the pinned upstream tree, the exact shared framework, `lean/Sheaf`,
  and DAG records found the source theorem and its two exact generic predicates.
  `Sheaf.Algebra.Homology.TorAmplitudeFlatModel` is about ring MODULES, not sheaves.
  The existing DAG constructibility and Tor predicates are the fixed-ring or
  constant-ring-sheaf constructions described above, not these categorical predicates.
  `tools/blueprint_refs.py search 'etale origin'` found only finite-coefficient
  blueprint notions; the generic source predicates have no definition nodes already.

Repairs: corrected only the item's statement and the forced statement-dependency list,
recorded full `statement_change`, and added two existing-definition node records. The
main existing theorem is retained; no duplicate module is written. Removed `:= by`
from `lean.statement` and stored the actual source signature ending before `:=`.
The new definition signatures are likewise verbatim source substrings. No dependency
module, private definition, proof, axiom, or new sorry has been written.

The source theorem's proof was read: apply the generic bounded-flat-model equivalence;
convert its strict support bounds to the explicit outside-interval IsZero condition;
reverse the representative isomorphism; and conversely recover the two strict bounds
from that IsZero condition. The source docstring explains K-flatness of bounded flat
complexes and truncation of a flat resolution using the Tor criterion. Since this is
an existing attachment, the published docstrings and proofs are not rewritten.

Compilation: scompile.py compiled both the original import/#print check and the
independent scratchpad/ReadSignatures.lean probe cleanly. The latter printed both
predicate bodies, ObjectProperty.flat, and the theorem's axioms. The axioms are exactly
propext, Classical.choice, and Quot.sound. All three existing declarations will also
be checked together by deliver2.py's prescribed existing-declaration probe.

Citer audit: exhaustive JSON inspection of stmt_deps and proof_deps finds exactly ONE
citer, `lem-sf-flat-model`; there is no second direct citer to open. I read its full
statement and proof, not just its references. Its assertion that the generic source is
an exact direct application is not justified with its recorded intrinsic finite-torsion
and constant-ring module interfaces. Accordingly `holds: false` flags that use, not a
counterexample to the parent theorem. A finite-stage constructibility and canonical
coefficient-encoding bridge is needed (compare `lem-sf-proetale-constructible-origin`).
The parent/unit statement is left untouched.

## New nodes

`def-sf-categorical-proetale-constructibility` records the existing
`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible` in
`WeilConjectures.SixFunctors.ProEtale.Derived.Constructible`, lines 78-88. I checked its
body, the etale bounded/constructible-cohomology definition, and
`ConstructibleSheaf/Defs.lean` (locally constant, finitely generated geometric stalks,
constructible locally closed strata). Its objects, concrete-category universes,
essential-image quantifiers and isomorphism direction match the node. Existing
finite-torsion/intrinsic or finite-ring etale-origin DAG notions do not state this
arbitrary concrete-category definition. Searches are recorded in the node and above.
The source constructs the actual essential-image object property; no hollow data is
introduced. All required new-node fields are included, with ancestor lem-sf-flat-model
and via path beginning with this item.

`def-sf-categorical-proetale-tor-amplitude` records the existing
`AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn` in
`WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitude`, lines 73-77. I unfolded its
abbreviation and read the generic TorAmplitude.lean definition: for every F, the
canonical derived tensor with singleFunctor F 0 has homology concentrated in [a,b].
No a<=b, constructibility or flatness hypothesis is built into the predicate. Its
category, monoidal assumptions and flat-resolution instance match the new node.
The ringed-site Tor-amplitude node uses a different category and is not this definition.
Searches are recorded in the node and above. This is reuse of existing real data,
without a new module, axiom or private copy; the complete new-node fields are present.

## Statement corrected

The old statement was:

> Let A be a commutative ring, let X be a scheme, let a b : ℤ with a ≤ b, and let K be an object of the derived category of sheaves of A-modules on the small pro-etale site of X such that K is bounded constructible. Then K has Tor amplitude in [a,b] if and only if there exists a cochain complex P of such sheaves with every term flat, with P^q zero for q outside [a,b], and with K isomorphic to the image of P in the derived category. Here the site and bounded constructibility are as in [def-weil-pbc-proetale-site] and [def-weil-finite-torsion-constructibility], and Tor amplitude is [def-weil-finite-tor-amplitude].

This incorrectly described the coefficient CATEGORY of the cited source as a ring,
omitted the source's ambient structures, and silently replaced its etale-origin
constructibility and categorical Tor predicates by different recorded definitions.
The corrected statement follows the full signature and predicate bodies of
WeilConjectures/SixFunctors/ProEtale/Derived/FlatModel.lean, theorem
`torAmplitudeIn_iff_exists_flatModel`, lines 56-70, together with its ambient binders
at lines 36-43. Every hypothesis and conclusion of that source is retained. The source
is a Lean module, not a Stacks tag, so its complete source context was read directly.

- `lem-sf-flat-model`: holds false for the claimed direct exact application, because
  its intrinsic finite-torsion constructibility and constant-ring SheafOfModules
  encoding need a bridge to the source's explicit categorical/etale-origin interface.
  The parent's mathematical assertion is not refuted and its statement is unchanged.

This is the complete citer list on the inspected DAG; no other node cites the item in
stmt_deps or proof_deps. Only the forced statement and dependency changes are recorded;
proof and proof_deps remain empty as on the base.

The first dry run accepted the source correction, citer audit, records and compilation,
but found that the current delivery base uses an empty item via path (the read-only
mirror still carried an older path). I adjusted the two new-node via lists to the
server-checked value [lem-sf-proetale-flat-model] and reran the prescribed dry run.
