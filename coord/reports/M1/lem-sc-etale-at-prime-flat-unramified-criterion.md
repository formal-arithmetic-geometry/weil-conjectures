## Worker report

The module states the pointwise étale criterion for a finitely presented commutative
algebra. It binds commutative rings `R,S`, an `R`-algebra structure, finite presentation,
and a prime ideal `q : Ideal S`. The first clause is `Algebra.IsEtaleAt R q`. The second
clause is an element `g` outside `q` for which the localized affine ring map, represented
by `(algebraMap S (Localization.Away g)).comp (algebraMap R S)`, is `RingHom.Etale`.
The third clause states flatness of the localized ring over `R` and subsingleton
localized Kähler differentials `LocalizedModule q.primeCompl (KaehlerDifferential R S)`.
The proof is `sorry` exactly as required for stage 2.

Dependencies are Mathlib leaves: `Algebra.FinitePresentation`, `Localization.AtPrime`,
`AlgebraicGeometry.Etale`/`RingHom.Etale`, `Module.Flat`, and `KaehlerDifferential`.
The edge cases checked were arbitrary prime ideals (including maximal and minimal primes),
`g` outside `q`, and zero localized differential modules via `Subsingleton`.

Searches found no existing project declaration and no exact Mathlib pointwise criterion:
`msearch.py leanfinder` and `loogle` searches for `IsEtaleAt`, flatness and Kähler
differentials; grep over Mathlib Etale, Smooth, Unramified, and Localization files; and
`rg` over `WeilConjectures` and `lean/Sheaf`.

The Lean statement renders the affine basic-open clause with the canonical localization
map and uses Mathlib's localized-module representation of vanishing differentials.

## Earlier second reading (a previous round; superseded)

The declaration and node were read together. All binders in the Lean signature are
explicit, the finite-presentation hypothesis and prime hypothesis are present, and the
three displayed propositions correspond to the node's three alternatives. The basic-open
map is rendered by the canonical `Localization.Away` algebra map; localized differentials
are rendered by `LocalizedModule` and `Subsingleton`.

## Second reading by M1

I read the sandbox node and module independently against the source and each of
its five statement dependencies. The unchanged node is the correct criterion;
the original Lean signature was not. The repaired signature says that (1) is
equivalent to (2), AND that (1) is equivalent to (3).

Source reading: the repository's `literature/stacks-project/algebra.tex` is absent
on this machine. I read the available Stacks source at
`/home/ubuntu/c1-stacks-review/algebra.tex`, including conventions (lines 32–44),
lemma-characterize-etale (39470), lemma-unramified-at-prime (41568), and
lemma-etale-flat-unramified-finite-presentation (41644). These are exactly the
labels and line positions named by the node. Rings are commutative with 1,
including the zero ring; contraction denotes inverse image, without injectivity.
00U6 assumes finite presentation and flatness of the local ring map; the
unramified lemma supplies its residue-field and maximal-ideal conditions.
08WD identifies étaleness with flatness, unramifiedness and finite presentation.
There is no standing field, characteristic, Noetherian, or nonzero assumption.

Object/hypothesis/conclusion inventory and matching:

- Commutative rings R and S: `{R : Type u} {S : Type v} [CommRing R]
  [CommRing S]`. Correct, with independent explicitly bound universes.
- Ring map R → S: `[Algebra R S]`, with map `algebraMap R S`.
  Correct: this describes an arbitrary unital map between commutative rings;
  it does not require an injective map.
- Finite presentation of S over R: `[Algebra.FinitePresentation R S]`.
  Correct. I opened the dependency's recorded declaration in
  `Mathlib.RingTheory.FinitePresentation`, line 44: finitely many polynomial
  variables, a surjection, and finitely generated kernel.
- Prime q of S: `(q : Ideal S) [q.IsPrime]`. Correct; no maximality imposed.
- Contracted prime p = q ∩ R: `q.under R`, the inverse image ideal under
  `algebraMap R S`. Correct; its prime instance is induced from q.
- Localization S_q: `Localization.AtPrime q`. Correct. The dependency's
  `Localization.AtPrime` in `Mathlib.RingTheory.Localization.AtPrime.Basic`,
  line 57, is localization at `q.primeCompl`, not at all nonzero elements.
- (1), formally étale S_q over R: `IsEtaleAt R q`. Correct. I opened
  `Mathlib.RingTheory.Etale.Locus`: its abbreviation is exactly
  `FormallyEtale R (Localization.AtPrime q)`.
- (2), existence of g outside q: `∃ g : S, g ∉ q ∧ ...`. Correct;
  its quantifier is inside the equivalence for the fixed q.
- (2), étale Spec(S_g) → Spec(R):
  `RingHom.Etale ((algebraMap S (Localization.Away g)).comp (algebraMap R S))`.
  Correct affine rendering of the very same map. I opened the dependency's
  `AlgebraicGeometry.Etale` in `Mathlib.AlgebraicGeometry.Morphisms.Etale`:
  its `HasRingHomProperty` instance identifies it with `RingHom.Etale`, and
  `AlgebraicGeometry.HasRingHomProperty.Spec_iff` in
  `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`, line 360, gives
  exactly the affine equivalence. Thus no private étale notion is introduced.
  The ring-map rendering also permits different universes for R and S.
- (3), S_q flat over R_p via the induced local map:
  `RingHom.Flat (Localization.localRingHom (q.under R) q (algebraMap R S) rfl)`.
  Correct. I opened `Localization.localRingHom` in the localization dependency,
  line 241: it maps the localization at the inverse image prime to that at q.
  `rfl` identifies the contraction, not an additional hypothesis.
  I opened `RingHom.Flat` in `Mathlib.RingTheory.RingHom.Flat`, line 27:
  it is precisely `Module.Flat` for the module structure induced by this map.
  The flatness dependency records both notions; `Module.Flat` in
  `Mathlib.RingTheory.Flat.Basic`, line 113, has the stated tensor-injectivity
  characterization for arbitrary modules.
- (3), localized Kähler differentials vanish:
  `Subsingleton (LocalizedModule q.primeCompl (KaehlerDifferential R S))`.
  Correct: an additive module is zero exactly when it is subsingleton.
  I opened `KaehlerDifferential` in `Mathlib.RingTheory.Kaehler.Basic`,
  line 153, and its universal derivation and linear-map equivalence; these
  supply the dependency's universal module. `LocalizedModule` in
  `Mathlib.Algebra.Module.LocalizedModule.Basic` is the module localization
  at the given multiplicative subset, here S minus q.
- All three conditions equivalent: the conclusion is `(A ↔ B) ∧ (A ↔ C)`.
  Correct: all six implications follow, with no condition asserted outright.

Mismatches and repairs:

1. Original conclusion `(A ↔ B) ↔ C` is a different proposition. For example,
   when A, B, C are all false, equivalence of the three conditions is true but
   that nested biconditional is false. Replaced it by `(A ↔ B) ∧ (A ↔ C)`.
2. Original clause (3) used `Module.Flat R (Localization.AtPrime q)`.
   Though flatness over R and over R_p here are equivalent, the node explicitly
   asks for flatness over R_p. Replaced it by flatness of the canonical
   `Localization.localRingHom`, using the dependency's existing `RingHom.Flat`.
3. Original `{R S : Type u}` unnecessarily tied their universes together.
   Replaced it by separate `Type u` and `Type v` binders.
4. Original theorem docstring only named four techniques. Expanded it to the
   node's four implication steps and their dependency ids, including the
   intermediate cotangent vanishings, local-ring identification, transitivity
   of flatness, base localization, and the product g₁g₂ construction.
5. Added the standard copyright/license header and removed the three direct
   imports already supplied through the two imports used by the statement.
   Updated `lean.statement` to the exact multiline signature in the file.

Edge cases: all prime ideals, including minimal and maximal primes, are covered.
The zero ring S has no prime q, so the quantification is vacuous, just as in the
node; no `Nontrivial` hypothesis is added. A unital map from the zero ring R
forces S to be zero and is likewise vacuous. Vanishing differential modules,
including zero modules, are represented exactly by `Subsingleton`. There are
no index sets, integer parameters or n to restrict; finite presentations with
zero generators or relations are allowed by the existing class. No restriction
on characteristic or perfectness is present. The independent universes u and v
are both explicitly bound; no new algebra or prime instance is assumed.

Independent searches (2026-10-11):

- `msearch.py ... leanfinder "etale local ring equivalent flat unramified finite
  presentation"`: eight hits, including `RingHom.etale_iff_formallyUnramified_and_smooth`,
  `Algebra.etaleLocus_eq_univ_iff_etale`, and étale localization meta-properties.
  None states the pointwise three-condition criterion.
- `msearch.py ... loogle "Algebra.IsEtaleAt, RingHom.Flat"`: zero hits.
- `msearch.py ... leansearch "Etale at a prime if and only if flat local
  homomorphism and zero differential module"`: service unavailable (Internal
  Server Error), recorded as unavailable, not evidence of absence.
- Independent `rg` for `isEtaleAt|IsEtaleAt|flat.*Unramified|etale.*Prime`
  across Mathlib Etale/Unramified, Smooth/Fiber and Flat/Localization, the
  entire source `WeilConjectures`, and repository `lean/Sheaf`: no exact match.
  `Algebra.exists_etale_of_isEtaleAt` only supplies (1) implies (2).
  `Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat` requires global flatness of S
  over R, not the node's pointwise hypothesis (its enclosing section was read).
  Source hits use existing local étale criteria or discuss other statements.
- `rg` of the full declaration name in Mathlib, `WeilConjectures`, `lean/Sheaf`,
  and `dag/lean_names_upstream.json`: no collision.

No new definition node, dependency module, private copy, or statement correction
is needed. All dependency records are usable. The mathematical node statement,
its hypotheses, source and proof are unchanged. There is one named theorem,
whose entire proof remains `by sorry`; there is no hollow definition or other
proved declaration. Every source/docstring tag and the 100-character line
limit were checked. Server compilation via `scompile.py` passed cleanly
(1.6 seconds), with no error or warning.
