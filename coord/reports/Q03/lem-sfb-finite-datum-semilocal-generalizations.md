## Worker report

The module `Sheaf.AlgebraicGeometry.InvariantAffineSemilocalGeneralizations` states
`AlgebraicGeometry.exists_invariant_affine_semilocal_generalizations`. Its sole proof
is `sorry`; it introduces no definition and changes only the item's `lean` record.
The statement, statement dependencies, proof plan and proof dependencies are unchanged.

Source read: Raynaud, *Un critère d'effectivité de descente*, primary scan
https://www.numdam.org/item/SAC_1967-1968__2__A5_0.pdf, printed p. 5-17
(the paragraph before Lemma 4.3 and Lemma 4.3), and p. 5-21 (beginning of reduction 6).
These passages construct the affine semilocal generalization scheme and establish
invariance as subfunctors using closedness of the relation maps. The node supplies
the explicit quasi-affine finite-set affine-neighbourhood extension and the empty case.
No source or node fault was found.

Hypothesis and clause correspondence:

- The schemes are `{Q S Z : Scheme.{u}}`; affine Q and S are `[IsAffine Q]`
  and `[IsAffine S]`. The finite surjection is `q : Q ⟶ S` with `[IsFinite q]`
  and `[Surjective q]`. There is no flatness hypothesis on q.
- The structure morphism is `z : Z ⟶ Q`. Noetherianity, explicitly defined in
  the node as locally Noetherian and quasi-compact, is
  `[IsNoetherian Z]`, whose parent classes are exactly those two conditions.
  This follows the shared STATE convention for new statements.
- The descent datum is `D : Over.DescentDatum q (Over.mk z)`, the dependency's
  transport encoding of the isomorphism with cocycle condition.
- R is `pullback (z ≫ q) q`, r0 is `pullback.fst (z ≫ q) q`, and r1 is
  the dependency's already defined canonical `D.toHom`. The latter transports
  the universal point; no arbitrary map or extra datum is substituted.
- The subset is `E : Set Z`, with finiteness `hE : E.Finite` and equality of
  inverse images `hInvariant : (pullback.fst (z ≫ q) q) ⁻¹' E = D.toHom ⁻¹' E`.
- `hQuasiAffine` supplies an open `W : Z.Opens` containing E and an open immersion
  `i : W.toScheme ⟶ A` into an affine scheme A, with `QuasiCompact i`.
  Such an open immersion identifies W with its open image, and quasi-compactness
  of i is exactly quasi-compactness of that open image in an affine target.
  Hence this renders the specified isomorphism to a quasi-compact open subscheme
  of an affine scheme, without assuming that W itself is affine.
- The existential witnesses are `L : Scheme.{u}` and `j : L ⟶ Z`.
  `IsAffine L`, `QuasiCompact j`, `Flat j`, and `Mono j` give precisely the
  four requested scheme/morphism properties. `pullback.isIso_diagonal_iff`
  in Mathlib.CategoryTheory.Limits.Shapes.Diagonal identifies `Mono j` with
  invertibility of the diagonal, the node's convention. Mathlib's
  `quasiCompact_iff_forall_isAffineOpen` identifies `QuasiCompact j` with the
  node's inverse-images-of-affine-opens convention.
- `Set.range j = {x : Z | ∃ e ∈ E, x ⤳ e}` is exactly the specified image:
  x specializes to some e in E, so x is a generalization of e.
- For every `T : Scheme.{u}` and `a : T ⟶ pullback (z ≫ q) q`, the final
  quantified equivalence says that `a ≫ r0` factors through j if and only if
  `a ≫ r1` does. By the fibre-product universal property these are exactly
  membership of a in the two pullback subfunctors of h_R. Since j is monic,
  each factorization is unique. Equality of these membership predicates is
  equality of the two subfunctors, rather than just equality of point images.
- `E ⊆ Set.range j` and `StableUnderGeneralization (Set.range j)` explicitly
  render the two stated image consequences.
- `Finite (MaximalSpectrum Γ(L, ⊤))` says precisely that the coordinate ring
  of the affine L has finitely many maximal ideals. It permits the zero ring.

Recorded statement dependencies used, with their source signatures/docstrings read:

- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- def-weil-finite-integral-morphism: Mathlib.AlgebraicGeometry.Morphisms.Finite,
  `AlgebraicGeometry.IsFinite`; the integral companion `IsIntegralHom` was read
  in Mathlib.AlgebraicGeometry.Morphisms.Integral but is not needed in this statement.
- def-pd-descent-datum: WeilConjectures.CategoryTheory.Comma.Over.DescentDatum,
  `CategoryTheory.Over.DescentDatum`, and its canonical `DescentDatum.toHom`.
- def-pc-fibre-product:
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback,
  `CategoryTheory.Limits.pullback` and `pullback.fst` (with scheme pullbacks).
- def-weil-open-immersion: Mathlib.AlgebraicGeometry.OpenImmersion,
  `AlgebraicGeometry.IsOpenImmersion`.
- def-weil-flat-morphism: Mathlib.AlgebraicGeometry.Morphisms.Flat,
  `AlgebraicGeometry.Flat`, whose `iff_flat_stalkMap` gives the node's local-ring convention.
- pqf-def-locnoeth: Mathlib.AlgebraicGeometry.Noetherian,
  `AlgebraicGeometry.IsLocallyNoetherian`. The recorded affine-cover equivalence
  and open-immersion/locally-finite-type permanence signatures were also read.

The statement dependencies are public imports. The stated proof dependencies have
plain imports: Ideal.Operations (prime avoidance), IdealSheaf.Subscheme and
Morphisms.ClosedImmersion (affine closed-subscheme/principal-open interface),
Spectrum.Prime.Topology (localization spectrum), Morphisms.Preimmersion
(localization monomorphism), Morphisms.QuasiSeparated, Morphisms.FinitePresentation
and Morphisms.Proper (permanence), Morphisms.QuasiFinite (finite fibres), and
PullbackCarrier (base-change images). Other proof modules are already public
statement imports: Scheme, Flat, Noetherian, Finite, DescentDatum and Inseparable.
The proof-only node lem-sfb-qc-flat-monomorphism-ringed-image has neither a Lean
record nor a Mathlib match in this snapshot, so there is no recorded module to
import for it. Its proof-plan use remains explicitly documented in step 7 of the
docstring. It supplies no notion needed to type this statement.

Edge cases checked before writing:

- Empty E: take Spec(0); the image is empty, both factorization subfunctors
  coincide, E is contained, generalization stability is vacuous, and the maximal
  spectrum is empty. No Nonempty E or nontrivial-ring restriction is imposed.
- Empty Z and empty base schemes are permitted. Existing structure maps and
  surjectivity enforce exactly their usual constraints.
- A singleton generic point is permitted. For comparable points, the maximal
  ideals of the localization correspond only to inclusion-maximal primes in
  the finite family. No closedness or incomparability hypothesis is added.
- Nonflat finite surjections remain allowed: invariance of the generalization
  hull uses the closed maps r0/r1 and specialization lifting.
- All scheme binders, including test schemes T and affine ambient A, use the
  same explicit universe u; every variable and universe is explicitly bound.
  This is the whole category Scheme.{u}, without a smaller test universe.

Searches:

- msearch.py leansearch: "A finite invariant set of points contained in a
  quasi-affine open has an invariant affine semilocal generalization subscheme".
  Eight hits on affine neighbourhoods, compact opens and Scheme.IsQuasiAffine,
  with no invariant semilocalization existence theorem. The latter class was
  read: it includes CompactSpace and immersion into Spec of global sections;
  its open-immersion theorem and of_isImmersion show its equivalence with the
  node's explicit open-immersion presentation used here. No new predicate is defined.
- msearch.py leanfinder: "A finite invariant subset of a Noetherian scheme with
  finite descent datum admits an invariant affine semilocal flat monomorphism
  with image its generalizations". Eight hits: affine transition limits, finite
  morphisms and Noetherian affine covers; none states invariant semilocalization.
- msearch.py loogle: "AlgebraicGeometry.Flat, CategoryTheory.Mono". Six hits:
  pushout-section monomorphisms, IsOpenImmersion.of_flat_of_mono and
  Flat.isIso_of_surjective_of_mono; none supplies this existence statement.
- msearch.py grep: "semilocal|semi.local|invariant.*monomorphism", subdirectory
  AlgebraicGeometry. Zero Mathlib hits.
- rg of WeilConjectures and Sheaf with
  "semilocal|semi.local|invariant.*monomorphism|generalization.*[Ss]ubscheme":
  semilocal ring/normalization/gluing and finite-flat relation results, but no
  invariant semilocal generalization-scheme existence theorem.
- grep -rn of the exact item id in WeilConjectures: no hits.
- rg of Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json with
  "exists_affine_semilocal|semilocal_generalizations|finite_datum_semilocal":
  no hits and no declaration-name collision.
- Source reads confirm the existing transport map `DescentDatum.toHom`,
  `StableUnderGeneralization`, `MaximalSpectrum`, and the affine-open
  quasi-compactness and diagonal-monomorphism equivalences; no private copies
  or new definition nodes are necessary.

Validation: the prescribed scompile.py, followed by deliver2.py --no-push and
normal deliver2.py. Compiler results are recorded by those delivery tools.

## Second reading by Q03

The dispatcher explicitly forbids starting another agent; this section records
my second pass over the completed node and Lean statement. The maintainer's
independent mathematical review remains the review specified by the assignment.
I checked every binder and conjunct against the unchanged node as listed above.
In particular the quasi-affine assumption retains an arbitrary open W embedded
in an affine scheme, the invariant relation uses canonical D.toHom, and the
subfunctor conclusion quantifies over morphisms from all test schemes in the
category. The generalization relation has the correct orientation x ⤳ e.
Empty E is allowed, and finiteness of maximal ideals does not require a
nonzero ring. The second pass replaced the equivalent split Noetherian hypotheses with the
shared class `[IsNoetherian Z]`, as required by coord/STATE.md. No mathematical
statement correction was needed.
