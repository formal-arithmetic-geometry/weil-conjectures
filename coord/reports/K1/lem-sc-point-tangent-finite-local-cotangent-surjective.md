## Worker report

The module `Sheaf.RingTheory.SurjectiveOfFiniteOfCotangent` states
`RingHom.surjective_of_finite_of_cotangent`, with one `sorry` and no new definitions.
The node is unchanged except for `lean`.

Hypothesis and clause correspondence:

- Local rings `(A,m)` and `(B,n)`: independently universe-polymorphic `A : Type u`,
  `B : Type v`, `[CommRing A]`, `[CommRing B]`, `[IsLocalRing A]`, `[IsLocalRing B]`.
  Their canonical maximal ideals are `IsLocalRing.maximalIdeal A` and
  `IsLocalRing.maximalIdeal B`.
- The local homomorphism is `(f : A →+* B) [IsLocalHom f]`.
- Finiteness is `hfinite : f.Finite`. Mathlib's definition uses `f.toAlgebra` and
  `Module.Finite A B`, so this means finite as a module, not finite as a set or merely
  finite type.
- The common residue field is `(k : Type w) [Field k]`, together with the named
  identifications `iA : IsLocalRing.ResidueField A ≃+* k` and
  `iB : IsLocalRing.ResidueField B ≃+* k`.
- Identity on that common field is
  `hres : iB.toRingHom.comp (IsLocalRing.ResidueField.map f) = iA.toRingHom`.
  This is the commuting residue-field square. The identifications do not posit any
  embedding of `k` into `A` or `B`, and hence include mixed-characteristic local rings.
- Surjectivity on `m/m² → n/n²` is `hcot : Function.Surjective
  (Ideal.mapCotangent (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B)
  f.toIntAlgHom (fun a ha => map_nonunit f a ha))`.
  `Ideal.mapCotangent` is Mathlib's actual quotient map. Reinterpreting `f` as a
  `ℤ`-algebra map changes neither its underlying function nor this quotient map.
  Surjectivity of this map as a function is exactly surjectivity on cotangent spaces;
  no choice of scalar structure changes the condition.
- The conclusion is `Function.Surjective f`.

Dependency declaration read:
`def-weil-locally-ringed-space-morphism` is a Mathlib leaf with
`AlgebraicGeometry.LocallyRingedSpace.Hom` in
`Mathlib.Geometry.RingedSpace.LocallyRingedSpace`. Its full structure and docstring were
read: the field `prop` requires `IsLocalHom` of each stalk map. The item cites this
node only for the meaning of a local ring homomorphism, so the statement uses exactly
that same Mathlib class, `[IsLocalHom f]`, directly. There is no locally ringed space
among the item's objects and no private replacement of the dependency. Importing the
geometric structure would be unused; its `IsLocalHom` class is available through
`Mathlib.RingTheory.Ideal.Cotangent`.

Other Mathlib signatures and docstrings read: `Ideal.Cotangent`, `Ideal.toCotangent`,
`Ideal.mapCotangent` and `Ideal.mapCotangent_toCotangent` in
`Mathlib.RingTheory.Ideal.Cotangent`; `IsLocalRing.ResidueField.map` in
`Mathlib.RingTheory.LocalRing.ResidueField.Basic`; `map_nonunit` in
`Mathlib.RingTheory.LocalRing.RingHom.Basic`; `RingHom.Finite` in
`Mathlib.RingTheory.Finiteness.Defs`; `RingHom.toIntAlgHom` in
`Mathlib.Algebra.Algebra.Hom`.

Source checked: the local literature checkout is absent on this machine, so opened
https://stacks.math.columbia.edu/tag/0E8M (Lemma 10.20.3). Its usual version also assumes
finite generation of `n`. The node explicitly removes that redundant hypothesis:
`B/mB` is a finite-dimensional local `k`-algebra, its maximal ideal `n/mB` is finitely
generated and equals its square, so Nakayama gives `n=mB`. The module docstring includes
all three node proof steps, including both named Nakayama dependencies. The stronger
form in the DAG is valid and needs no statement correction.

Edge cases checked before writing: fields have zero cotangent spaces and the common
residue-field condition makes the map an isomorphism; identity maps and proper quotient
maps meet the criterion; `k → k[ε]/(ε²)` fails cotangent surjectivity and is not falsely
included; a proper finite field extension fails the common-field identity condition.
No Noetherian hypothesis, finite-generation hypothesis on `n`, characteristic restriction,
or equal-universe restriction is imposed. The zero ring is already excluded by the
standard nontrivial local-ring/residue-field convention, as in the source.

Searches (all remote search commands use `msearch.py K1
lem-sc-point-tangent-finite-local-cotangent-surjective`; exact queries also logged in
`searches.jsonl`):

- LeanSearch: `finite local ring homomorphism inducing isomorphism on residue fields and
  surjection on cotangent spaces is surjective`. Service returned HTTP 500; no absence
  conclusion drawn from this unavailable service.
- LeanFinder: `finite local ring homomorphism surjective if residue field isomorphism and
  cotangent map surjective`. Eight hits, including `IsLocalRing.residue_surjective`,
  `Ideal.algebraMap_residueField_surjective`, and unrelated cotangent-complex results;
  none states the criterion.
- Loogle: `Ideal.Cotangent`. Twelve hits identify the standard quotient definition and
  related infrastructure, not the criterion.
- Mathlib grep: `cotangent.*surjective|surjective.*cotangent|mapCotangent`, subdirectory
  `RingTheory`. Quotient-map, cotangent-complex and completion results, no exact criterion.
- Direct `rg` of Mathlib's `Ideal/Cotangent.lean` and local-ring modules found the map
  and residue-field APIs used above. Direct `rg` for
  `finite.*cotangent|surjective.*cotangent|cotangent.*surjective` over the upstream
  `WeilConjectures` and project's `lean/Sheaf` found finite-field-algebra generator and
  Hopf-algebra results with different statements, no exact criterion. A search for the
  item's id in the upstream source had no hits. The proposed full declaration name was
  checked in `dag/lean_names_upstream.json`, Mathlib and upstream source, with no hits.

Validation: `scompile.py` compiled the module cleanly on the server in 1.3 s. No warnings.
No node faults or disputed statements found. No new nodes or dependency modules needed.


## Second reading by K1

I independently opened the node copy, the delivered Lean module, the sole statement
dependency node and its Mathlib declaration, and the Mathlib definitions used in the
signature. No statement mismatch was found; the Lean and node record are unchanged.
The only change is this independent review appended to the report.

Object, hypothesis and conclusion checklist (all verdicts: exact):

- Objects: the commutative local rings A and B are `{A : Type u} {B : Type v}`,
  `[CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]`. Their m and n are
  `IsLocalRing.maximalIdeal A` and `IsLocalRing.maximalIdeal B`; these are the ideals
  of nonunits, not arbitrary chosen ideals.
- Object and hypothesis: the local homomorphism A → B is `(f : A →+* B)` with
  `[IsLocalHom f]`. I read `AlgebraicGeometry.LocallyRingedSpace.Hom` in
  `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`: its `prop` field uses precisely
  `IsLocalHom` on the stalk maps. The dependency node cites this structure to describe
  locality; this algebraic item introduces no spaces or stalks. Using that underlying
  Mathlib class directly is appropriate and introduces no private notion or extra
  geometric hypothesis. `map_nonunit f` supplies the maximal-ideal inclusion.
- Hypothesis: finite means `(hfinite : f.Finite)`. I read
  `Mathlib.RingTheory.Finiteness.Defs`: it installs `f.toAlgebra` and asserts
  `Module.Finite A B`. No injectivity or finite-type replacement is imposed.
- Object: the common residue field is `(k : Type w) [Field k]`, with
  `iA : IsLocalRing.ResidueField A ≃+* k` and
  `iB : IsLocalRing.ResidueField B ≃+* k`. These specify the two identifications in
  the node's notation (A,m,k) → (B,n,k), without coefficient-field embeddings.
- Hypothesis: identity on that field is
  `hres : iB.toRingHom.comp (IsLocalRing.ResidueField.map f) = iA.toRingHom`.
  I read the definition of `ResidueField.map`: it descends the same f by the
  maximal ideals. Composing with the two equivalences is exactly the identity
  requirement, and implies the source's residue-field isomorphism requirement.
- Hypothesis: cotangent surjectivity is `hcot : Function.Surjective
  (Ideal.mapCotangent (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B)
  f.toIntAlgHom (fun a ha => map_nonunit f a ha))`. I read `Ideal.Cotangent`,
  `toCotangent_eq`, `mapCotangent`, and `mapCotangent_toCotangent` in
  `Mathlib.RingTheory.Ideal.Cotangent`: the quotient is m/m² and the map sends
  the class of a to the class of f(a). `RingHom.toIntAlgHom` retains f's exact
  underlying function. The use of ℤ-linear maps requires no additional algebra
  hypothesis; function surjectivity is the same condition as surjectivity of the
  k-linear cotangent map under the common-field identifications.
- Conclusion: `Function.Surjective f` is precisely surjectivity of A → B.
  All objects precede their hypotheses and the conclusion; no extra instances,
  Noetherianity, characteristic or maximal-ideal finiteness are present.

Source reading: the local Stacks checkout is absent. I read the actual algebra.tex
lemma `lemma-when-surjective-local` and the chapter conventions from
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex, and checked
Tag 0E8M at https://stacks.math.columbia.edu/tag/0E8M. Rings are commutative with 1.
The source has an additional finite-generation assumption on n, expressly removed
by this node's source record and reviewed stage-1 proof. This removal is valid:
B/mB is a finite-dimensional k-algebra and local; its maximal ideal n/mB is therefore
finitely generated over B/mB. Cotangent surjectivity gives n = mB + n²; the ideal
n/mB equals its square and is contained in the Jacobson radical. Nakayama makes it
zero. Finally the finite A-module B has quotient generated by 1, so Nakayama over A
makes 1 generate B. The delivered docstring faithfully records these three steps,
including both proof-dependency node names. No statement correction is needed,
and there are no new definition nodes or dependency modules to review.

Edge cases: A and B fields give zero cotangent spaces, and hres forces f to be an
isomorphism. A proper finite extension of fields cannot satisfy hres. The finite map
k → k[ε]/(ε²) satisfies the residue condition but fails hcot. Identity maps and
surjective maps to nonzero local quotients are covered. The zero ring has no residue
field or maximal ideal and is excluded by the node's (A,m,k) data as well as
Mathlib's nontrivial local-ring class. Empty schemes, empty index sets and n = 0 as
an integer are not objects in this statement; a zero maximal ideal is covered.
Arbitrary characteristic, mixed characteristic, non-Noetherian local rings, and
independent universes u, v, w are allowed. Every variable and universe is bound.

Independent searches, using different queries from the first worker:

- LeanFinder via msearch: “A module-finite morphism between local commutative rings
  is onto when its residue morphism is bijective and its maximal ideal modulo square
  map is onto”. Eight hits on residue-field surjectivity, stalkwise surjectivity and
  finiteness of residue fields, none the criterion.
- Loogle via msearch: `RingHom.Finite, Function.Surjective`. Three hits:
  `RingHom.Finite.of_surjective`, `RingHom.surjective_of_epi_of_finite`, and
  `RingHom.surjective_iff_epi_and_finite`. Their signatures use surjectivity as a
  hypothesis or categorical epimorphism, not the local/cotangent criterion.
- Mathlib grep via msearch: `surjective.*(local|[Cc]otangent)|([Cc]otangent|local).*surjective`
  in RingTheory. Localized-module and local-spectrum results; no exact statement.
- Direct rg over all Mathlib, upstream WeilConjectures and project lean/Sheaf for
  `surjective.*cotangent|cotangent.*surjective|surjective_of_finite_of_cotangent`
  found only cotangent-complex surjectivity results. Broader `cotangent|Cotangent`
  searches in upstream/project found finite-field-algebra generator results and
  Hopf algebra material with different hypotheses. The proposed declaration name
  and item id have no upstream-name-index or upstream source match. No existing
  statement warrants dropping this module.

H5/H6/H8/H9 checks: no new definitions and hence no hollow data; exactly one theorem
with proof `by sorry`; standard RingHom namespace and topic directory; both imports
are used by the signature; module and theorem docstrings contain the source and
blueprint id; all lines fit 100 characters. I compared the node's lean.statement
verbatim with the signature, and they agree.

Validation: independent scompile.py run returned exit code 0, compiled in 1.4 s,
with no warnings or errors. No mathematical or Lean changes were necessary.
