## Worker report

Module `Sheaf.AlgebraicGeometry.SmoothAtPrimeArtinianLifting` states
`AlgebraicGeometry.smooth_on_open_iff_artinian_lifting`. Its only proof is `sorry`.
The declaration docstring carries all twelve proof steps and names their DAG inputs.
No definition, new node, dependency module, or statement correction is needed.

Hypothesis and clause correspondence:

- Commutative rings R and A: `{R A : Type u} [CommRing R] [CommRing A]`.
- R Noetherian: `[IsNoetherianRing R]`.
- The specified ring map and finite generation of its algebra:
  `(φ₀ : R →+* A) (hfinite : φ₀.FiniteType)`.
  `RingHom.FiniteType` uses the algebra structure supplied by this exact ring map.
- The prime ideal: `(q : Ideal A) [q.IsPrime]`.
- The affine schemes and π: `Spec (CommRingCat.of A)` and
  `Spec.map (CommRingCat.ofHom φ₀)`; the codomain is Spec R.
- (1), the open subset and its open subscheme: `∃ W : (Spec (CommRingCat.of A)).Opens`.
  `W.ι` is the inclusion of precisely that open subscheme.
- Containment of q: `(⟨q, inferInstance⟩ : PrimeSpectrum A) ∈ W`.
- Smoothness of π restricted to W:
  `Smooth (W.ι ≫ Spec.map (CommRingCat.ofHom φ₀))`.
- Equivalence of (1) and (2): the outer `↔`.
- Every pair of Artinian local rings B' and B: the `∀` type binders and all four
  `[IsArtinianRing ...]`, `[IsLocalRing ...]` binders.
- Every small extension: `(φ : B' →+* B)`, `Function.Surjective φ`, and
  `Module.length B' (RingHom.ker φ) = 1` give exactly Definition 02HS inline.
  In particular, no square-zero hypothesis replaces the length-one condition.
- Every ρ and a: `∀ (ρ : R →+* B') (a : A →+* B)`.
- Compatibility: `a.comp φ₀ = φ.comp ρ`.
- The preimage maximal ideal: `Ideal.comap a (IsLocalRing.maximalIdeal B) = q`.
- The required ring homomorphism: `∃ a' : A →+* B'`.
- Both equations for the lift: `φ.comp a' = a ∧ a'.comp φ₀ = ρ`.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` in
  `Mathlib.RingTheory.Noetherian.Defs`; its definition/docstring says ideals are
  finitely generated. Imported transitively through the finite-type/length imports.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `.Spec.map` in
  `Mathlib.AlgebraicGeometry.Scheme`; read their full signatures and docstrings.
  Imported transitively by the smooth-morphism import.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth` in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`; read the class signature and affine
  chart definition. This is the recorded smooth scheme-morphism notion.
- Additional standard notions: `RingHom.FiniteType`, `Module.length`, `RingHom.ker`,
  `IsArtinianRing`, `IsLocalRing`, and `IsLocalRing.maximalIdeal`.

Edge cases checked before writing:

- A zero ring has no prime q, exactly as the premise requires; no extra nonzero
  assumption on A or R is imposed. A prime q excludes an empty affine spectrum.
- W cannot be empty because it must contain q; there is no hidden affine or
  principal-open restriction on W.
- Artinian local rings are nonzero by Mathlib's local-ring convention, as in Stacks.
  An isomorphism has zero-length kernel and is not a small extension.
- No restriction on residue characteristic, residue field size, or relative dimension.
- R and A share the ambient scheme universe; any two rings fit in a common universe.
  Tests are in `Type (max u v)`, so their universe is never below the base-ring universe.
  The canonical Artinian test quotients needed for the reverse implication fit there,
  while v permits larger test rings. Every universe and variable is explicitly bound.
- Maps ρ and a are ring maps, not restricted to a prechosen algebra structure;
  the compatibility equation provides precisely their required R-linearity.

Searches for an existing statement (2026-10-11):

- `msearch.py ... leansearch "smooth at prime Artinian local small extension lifting criterion"`:
  unavailable, Internal Server Error (no verdict inferred).
- `msearch.py ... leanfinder "A finite type algebra over a Noetherian ring is smooth at a prime
  if and only if maps lift along small extensions of Artinian local rings"`: eight hits,
  including `Algebra.IsSmoothAt`, `Algebra.smooth_iff`, `Algebra.Smooth`,
  `Algebra.IsSmoothAt.exists_notMem_smooth`; none is the Artinian lifting criterion.
- `msearch.py ... loogle "Module.length, RingHom.ker, IsArtinianRing"`: zero hits.
- `msearch.py ... grep "SmallExtension|small extension|smooth.*[Aa]rtinian" RingTheory`:
  zero hits.
- `rg` in Mathlib for the dependency signatures and module length found the recorded
  declarations and `Module.length` in `Mathlib/RingTheory/Length.lean`.
- `rg` in WeilConjectures and project `lean/Sheaf` for
  `smallExtension|SmallExtension|artinian.*lifting|smooth.*artinian|IsSmoothAtPrime|`
  the item id: only existing smooth-at-prime definitions and unrelated downstream
  uses; no matching criterion. `Algebra.IsSmoothAtPrime` is a principal-localization
  predicate, while this node explicitly asks for an open smooth neighbourhood;
  the statement retains that neighbourhood and its scheme map directly.
- Exact declaration-name search in `dag/lean_names_upstream.json`, `lean/Sheaf`, and
  `WeilConjectures` for `smooth_on_open_iff_artinian_lifting`: no match.

Source checked: the referenced local `literature/stacks-project/algebra.tex` is absent
on this machine. Read the primary sources at
[Stacks 02HT](https://stacks.math.columbia.edu/tag/02HT) and
[Stacks 02HS](https://stacks.math.columbia.edu/tag/02HS).
The node agrees with the equivalence (1) iff (3) and the small-extension definition.
No statement dispute or mathematical fault was found.

## Second reading by F1

Independent second reading on 2026-10-11. I opened the node copy, the complete
Lean module, all three statement-dependency nodes and their Mathlib declarations.
Verdict: the Lean states exactly the node; no mathematical or signature repair
was needed. Only this independent review section was added.

Source first: the repository has no local Stacks algebra.tex, so I fetched the
primary Stacks TeX into sandbox-only algebra-source.tex and read lines 38933–38994
(section-smooth-Noetherian, definition-small-extension, lemma-smooth-test-artinian)
and 37510–37517 (definition-smooth-at-prime). There is no section-wide additional
hypothesis. I also read [02HT](https://stacks.math.columbia.edu/tag/02HT),
[02HS](https://stacks.math.columbia.edu/tag/02HS),
[00TB](https://stacks.math.columbia.edu/tag/00TB),
[01V6](https://stacks.math.columbia.edu/tag/01V6), and
[02H6](https://stacks.math.columbia.edu/tag/02H6).
The source's prime p is the contraction of q, not extra input restricting q.
The node explicitly chooses the open-neighbourhood formulation of smoothness;
01V6 and 02H6 justify its agreement with 00TB and the recorded scheme predicate.

Object, hypothesis and conclusion checklist (each verdict is exact):

- Commutative rings R and A: `{R A : Type u} [CommRing R] [CommRing A]`.
- R Noetherian: `[IsNoetherianRing R]`; no local, field, or domain assumption.
- Specified map R to A: `(φ₀ : R →+* A)`; finite generation as an algebra
  for that map: `(hfinite : φ₀.FiniteType)`.
- Prime q of A: `(q : Ideal A) [q.IsPrime]`.
- Affine spectra and π: `Spec (CommRingCat.of A)` and
  `Spec.map (CommRingCat.ofHom φ₀)`, with codomain Spec R.
- Existence of an arbitrary open subset W: `∃ W : (Spec (CommRingCat.of A)).Opens`.
- W contains q: `(⟨q, inferInstance⟩ : PrimeSpectrum A) ∈ W`.
- W has its open subscheme structure: the domain of `W.ι` is Mathlib's
  `Scheme.Opens.toScheme W = X.restrict W.isOpenEmbedding`.
- Smoothness of π restricted to that open subscheme:
  `Smooth (W.ι ≫ Spec.map (CommRingCat.ofHom φ₀))`.
- Equivalence of the two conditions: the outer `↔`.
- Arbitrary B' and B, both commutative Artinian local rings:
  `∀ (B' B : Type (max u v)) [CommRing B'] [CommRing B]` followed by
  `[IsArtinianRing B'] [IsArtinianRing B] [IsLocalRing B'] [IsLocalRing B]`.
- Arbitrary small extension: `(φ : B' →+* B)`, followed by
  `Function.Surjective φ → Module.length B' (RingHom.ker φ) = 1 →`.
  The kernel is the ideal of B', with its B'-module structure. This is precisely
  the length in the definition, not length over B or over the residue field.
- Every base map ρ and top map a: `∀ (ρ : R →+* B') (a : A →+* B)`.
- Commutativity of the given diagram: `a.comp φ₀ = φ.comp ρ →`.
- The prescribed closed-point inverse image:
  `Ideal.comap a (IsLocalRing.maximalIdeal B) = q →`.
- Existence of a ring map a' after all those inputs and hypotheses:
  `∃ a' : A →+* B'`.
- Its two required equations, with no uniqueness or residue-field restriction:
  `φ.comp a' = a ∧ a'.comp φ₀ = ρ`.

Dependency check: `IsNoetherianRing` (Noetherian/Defs.lean:196) is
`IsNoetherian R R`, hence finite generation of every ideal. `Spec` and `Spec.map`
(Scheme.lean:470,479) are the scheme spectrum and the contravariant map from the
exact φ₀. `Smooth` (Morphisms/Smooth.lean:62) quantifies over affine charts and
requires their ring maps smooth; it is the recorded dependency notion, identified
with locally finite presentation plus formal smoothness by 02H6. I read
`RingHom.FiniteType` (FiniteType.lean:217): it uses `φ₀.toAlgebra`, so there is no
unrelated algebra instance. `Module.length` (Length.lean:32) is module length;
`RingHom.ker` (Ideal/Maps.lean:745) is the domain ideal defined by comap of zero.
`IsArtinianRing` is the descending-chain condition for ideals in the commutative
case. `IsLocalRing` requires a nontrivial ring, and `maximalIdeal` is its nonunits
ideal. No dependency is unusable and no private notion was introduced.

Edge cases: a zero A has no prime q, exactly as in the source; a zero R cannot
map to a nonzero A with a prime, so no extra nontriviality binder is needed.
An empty W is excluded solely by q membership; W is not required affine or
principal. Local test rings are nonzero, consistently with Stacks. An identity
extension has kernel length zero and is excluded; general square-zero kernels
are not substituted for length one. There is no residue-field-isomorphism
hypothesis (that would be source condition (4)), nor any characteristic or
relative-dimension restriction. No index family or n occurs in the signature;
finite presentations with zero generators remain covered. Rings R and A can
be placed in any common ambient universe; tests in `Type (max u v)` include
canonical quotients/localizations of the finite presentation and permit larger
rings. This avoids a lifting condition vacuous in a universe below u. Both
universes are declared explicitly; all variables and instances are bound.

Independent searches, with different words from the first reader:

- LeanFinder via msearch: "infinitesimal criterion smooth neighbourhood lifting
  homomorphisms Artin rings kernel length one" returned eight hits. I checked
  `Algebra.FormallySmooth.exists_lift` and related lifts in Smooth/Basic.lean:
  they concern arbitrary nilpotent quotient lifts under formal smoothness, not
  this primewise Artinian equivalence. Other hits were `RingHom.smooth_def` and
  locally standard smoothness characterizations; none duplicates this statement.
- Loogle via msearch: `IsArtinianRing, RingHom, Smooth` could not resolve the
  unqualified Smooth; the corrected query `IsArtinianRing, RingHom.ker` returned
  zero hits. The first query is not treated as a negative search result.
- LeanSearch via msearch: "finite type Noetherian algebra smooth near prime iff
  lifting along Artinian local surjections with simple kernel" was unavailable
  (Internal Server Error); no mathematical verdict is inferred from it.
- rg over Mathlib/RingTheory, WeilConjectures, and project lean/Sheaf using
  `small.?extension`, `smooth.{0,60}artin`, `artin.{0,60}smooth`,
  `artin.{0,60}lift`, and `lift.{0,60}artin` found no matching criterion.
  Project EtaleInfinitesimalNeighbourhoods refers to the downstream scheme-point
  criterion, not this ring criterion. Upstream Artinian/Ring.lean:98 uses a
  formal-smooth lift to obtain roots of units, a different theorem.
- Exact-name search across the source, project and dag/lean_names_upstream.json
  found no pre-existing `smooth_on_open_iff_artinian_lifting`. I opened the
  project's `Algebra.IsSmoothAtPrime` in SingularIdeal.lean:23: it defines
  smoothness on a principal localization, not the Artinian equivalence. The
  present file defines no replacement predicate; it directly uses the node's
  open subset, recorded Spec map and recorded Smooth.

H5–H9: no definitions or instances are added, and the sole theorem has proof
`by sorry`. The module and declaration docstrings name 02HT/02HS and the correct
blueprint id. I compared all twelve numbered docstring proof steps with the
node: principal-open identification, small-extension kernels, forward lifting,
presentation/conormal sequence, reduction to splitting, localization, Artinian
quotients, length-one filtration, section, conormal retraction, Artin-Rees and
differential comparison, and splitting after completion are all retained with
their named inputs. No line exceeds 100 characters; imports supply the smooth
predicate, finite-type hypothesis, length, and local-ring structure. Namespace
and header agree with the project conventions.

No new node, dependency module, or statement correction is part of this delivery;
there are no new-node/dependency-module/correction citer reviews to perform.
The node's lean.statement was checked verbatim against the file signature and
matches. The server scompile check succeeded in 1.8 seconds with no warnings.
The initial compile invocation used a repository-relative path absent from the
read-only checkout; rerunning from the sandbox fixed that path issue without
changing any Lean. Mismatches found: none. Changes: report only.
