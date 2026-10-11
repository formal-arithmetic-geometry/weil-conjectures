## Worker report

The module `lean/Sheaf/AlgebraicGeometry/FiniteOverCompleteLocalProduct.lean` states
`Algebra.finite_over_complete_local_product` with `sorry` proof. It uses `CommRing R` and
`CommRing S`, `IsNoetherianRing R`, `IsLocalRing R`, and
`IsAdicComplete (IsLocalRing.maximalIdeal R) R` for the complete Noetherian local base,
and `[Algebra R S] [Module.Finite R S]` for the finite algebra map.

The first conjunction renders the conclusions clause by clause: `@IsNoetherianRing S _`
for Noetherianity; `Finite {M : Ideal S // M.IsMaximal}` for finitely many maximal ideals;
and an existential finite index type `ι`, `Fintype ι`, and family `T : ι → CommRingCat`.
For every factor it states `@IsNoetherianRing (T i) _`, `@IsLocalRing (T i) _`, and
existence of a local-ring instance `h` under which
`IsAdicComplete (IsLocalRing.maximalIdeal (T i)) (T i)` holds. The factorization is a
ring equivalence `Nonempty (S ≃+* (∀ i, T i))`.

The final implication is the domain clause. For an explicit `hD : IsDomain S`, it repeats
Noetherianity, supplies `hL : IsLocalRing S`, states completeness for the maximal ideal
under that instance, and asserts `∃! M : Ideal S, M.IsPrime ∧
Ideal.comap (algebraMap R S) M = IsLocalRing.maximalIdeal R`, expressing the unique prime
over the maximal ideal of `R`.

Dependencies used are the Mathlib declarations `IsNoetherianRing` from
`Mathlib.RingTheory.Noetherian.Defs`, `IsAdicComplete` from
`Mathlib.RingTheory.AdicCompletion.Basic`, and `Module.Finite` from
`Mathlib.RingTheory.Finiteness.Defs`. The module imports
`Mathlib.RingTheory.AdicCompletion.LocalRing`, `Mathlib.RingTheory.Finiteness.Defs`, and
`Mathlib.RingTheory.Noetherian.Defs`.

Edge cases checked: the finite index type may be empty (the zero-product case), and no
nonemptiness or positive cardinality was added; the domain implication is conditional on
`IsDomain S`; explicit local-ring witnesses are used before referring to maximal ideals.
The file compiled cleanly with `scompile.py` (only the expected `sorry` proof).

Searches made: `rg -n "finite_over_complete_local_product"` over the source and project
Lean trees found no existing declaration. The node's recorded Mathlib searches (LeanSearch,
LeanFinder, Loogle, and grep over AdicCompletion/LocalRing and Henselian) found no theorem
for this finite-algebra decomposition, so a new statement module was required.

## Earlier second reading (a previous round; superseded)

The statement was read against Stacks Tag 0325 and the node text. Every hypothesis and each
product/domain clause is represented in the signature; no proof content is included beyond
`sorry`.

## Second reading by F1

I independently read the item node, all three statement-dependency nodes, their
recorded Mathlib definitions, the delivered Lean, and Stacks algebra.tex at
lemma-quotient-complete-local (0325), lines 44811–44822. This machine does not
have literature/stacks-project/algebra.tex; I read the available Stacks source
at /home/ubuntu/c1-stacks-review/algebra.tex, including its conventions at line
36, complete-local-ring definition at lines 44789–44803, and
lemma-completion-finite-extension (07N9) at lines 23135–23173. The source
assumes commutative unital rings, permits the zero ring, and requires precisely
a Noetherian complete local base and a finite ring map. The item's domain
clause follows from its product assertion and the integral prime-over-maximal
argument, as its node says.

Object/hypothesis/conclusion checklist, after repair:

- Objects R and S: `(R : Type u) (S : Type v) [CommRing R] [CommRing S]`.
  Verdict: the same arbitrary commutative unital rings, independently sized.
- Noetherian R: `[IsNoetherianRing R]`. Verdict: exact; the dependency
  def-weil-pbc-noetherian-ring records `IsNoetherianRing`, the abbreviation
  `IsNoetherian R R` (Noetherian/Defs.lean:196), equivalently every ideal FG.
- Local R and its maximal ideal m: `[IsLocalRing R]` and
  `IsLocalRing.maximalIdeal R`. Verdict: exact. LocalRing/Defs.lean:30 includes
  Nontrivial, consistent with a local ring having a unique maximal ideal.
- m-adically complete R: `[IsAdicComplete (IsLocalRing.maximalIdeal R) R]`.
  Verdict: exact; def-weil-pbc-adically-complete-ring records this same
  Mathlib notion. Basic.lean:56 includes Hausdorffness and precompleteness;
  `AdicCompletion.of_bijective_iff` at line 647 identifies it with bijectivity
  of the canonical completion map, including separatedness.
- Ring map R → S: `[Algebra R S]`, used as `algebraMap R S` in the final
  comap. Verdict: exact, since a map from a commutative ring induces an
  algebra structure, with no injectivity or local-map assumption added.
- S finitely generated over R: `[Module.Finite R S]`. Verdict: exact;
  def-weil-finitely-generated-module records this class, whose field is
  `(⊤ : Submodule R S).FG` (Finiteness/Defs.lean:117).
- S Noetherian: first conjunct `@IsNoetherianRing S _`. Verdict: exact.
- Finitely many maximal ideals: `Finite {M : Ideal S // M.IsMaximal}`.
  Verdict: exact, counting all maximal ideals, without a nonempty requirement.
- A finite product: `∃ (ι : Type v) (_ : Fintype ι)
  (T : ι → CommRingCat.{v}), ... Nonempty (S ≃+* (∀ i, T i))`.
  Verdict: exact ring isomorphism; no algebra compatibility is asserted in
  the node, and no positivity or chosen ordering of the factors is required.
- Each factor Noetherian: `(∀ i, @IsNoetherianRing (T i) _)`. Verdict: exact.
- Each factor local: `(∀ i, @IsLocalRing (T i) _)`. Verdict: exact.
- Each factor complete for its maximal ideal: `(∀ i, ∃ h : IsLocalRing (T i),
  let _ := h; IsAdicComplete (IsLocalRing.maximalIdeal (T i)) (T i))`.
  Verdict: exact. Local-ring structures are propositions, so the separate
  existential witness and local conjunct do not name different notions.
- Conditional domain clause: `∀ hD : IsDomain S, ...`. Verdict: the same
  conditional conclusion, with no domain assumption in the general clause.
- Domain S is Noetherian, local, complete: `@IsNoetherianRing S _ ∧
  ∃ hL : IsLocalRing S, let _ := hL;
  IsAdicComplete (IsLocalRing.maximalIdeal S) S ∧ ...`. Verdict: all present.
- Its maximal ideal n is the only prime over m: `∃! M : Ideal S,
  M.IsPrime ∧ Ideal.comap (algebraMap R S) M = IsLocalRing.maximalIdeal R`.
  Verdict: exact in the stated context. Finiteness makes the map integral;
  a prime over m is maximal (00GS(2)), and locality makes that maximal ideal
  n. Thus the existential unique prime cannot be some other ideal.

Edge cases: S may be zero and ι may be empty, yielding the zero product; no
Nontrivial S instance is assumed except conditionally through IsDomain S.
The zero base is excluded by the source's local-ring assumption. Fields,
positive and zero characteristic, and non-domains are included. There is no
scheme or cohomological degree in this statement. Arbitrary finite cardinality,
including zero, is covered. R and S have independent universes u and v; factors
can be quotient rings of S in Type v and a finite index can be lifted to Type v.
A server `#check` with `pp.universes` confirms the repaired declaration has
exactly universe parameters u and v, with no unbound variables.

Independent searches (not just the first worker's theorem name):

- LeanSearch via msearch: "A module finite algebra over a complete local
  Noetherian ring splits into finitely many complete local rings". Service
  returned Internal Server Error; recorded as unavailable, no verdict claimed.
- Loogle via msearch: `IsAdicComplete, Module.Finite`. Successful, no hits.
- LeanFinder via msearch: "A finite algebra over an adically complete
  Noetherian local ring decomposes as a product of complete local rings".
  Eight hits: completion/product-module equivalences, complete implies
  henselian, Hausdorffness, completeness forces locality, completion tensor
  comparison, finite quotients. None states the finite-algebra decomposition.
- Mathlib grep via msearch, RingTheory: `prod.*(complete|local)|finite.*henselian|
  finite_over_complete`. Opened the plausible hits: Artinian/Module.lean
  `IsArtinianRing.quotNilradicalPowEquivPi` assumes Artinianity and decomposes
  a quotient; Spectrum/Prime/Topology.lean
  `MaximalSpectrum.toPiLocalizationEquiv` assumes discrete prime spectrum.
  Neither is the statement here. Henselian.lean supplies complete-to-henselian,
  not this theorem. No exact declaration exists.
- `rg` on WeilConjectures and lean/Sheaf with `finite_over_complete`,
  `finite.*complete.*local`, `product.*local rings`, `prod.*henselian`: only
  a proof citation and `finite_algebra_is_product_local_rings` in
  EtaleRetractionFiniteProductLocal.lean. I opened that theorem: it assumes
  pointed étale retractions and concludes local factors only, without
  Noetherianity/completeness. It is not this item. Also checked the upstream
  name index; no declaration collision.

Mismatches and repairs:

1. H3 universes: original Lean `#check` exposed four independent universes,
   with arbitrary factor universe u_4 independent of S's u_2. This requires
   potentially large S to split into small factors for every universe choice,
   a stronger conclusion than the node. Fixed explicit `universe u v`,
   `R : Type u`, `S : Type v`, `ι : Type v`, `CommRingCat.{v}`. No node-text
   correction was needed: the node and source already state the right theorem.
2. H8: the theorem docstring had no natural-language proof. Added the node's
   six steps, all dependency identifiers, the filtration identification,
   localization/completion argument, empty-product case and domain argument.
3. H9: supplied the standard copyright/license/authorship header and moved
   the commutative-algebra module from AlgebraicGeometry to RingTheory;
   updated lean.module and lean.file accordingly. The recorded lean.statement
   is now copied verbatim from the declaration's signature.

No new definition nodes or dependency modules were needed; all three
statement-dependency declarations are usable and used. No definition has data
filled by sorry; the only theorem proof remains `by sorry`, as stage 2 requires.
The node statement, hypotheses and six proof steps were otherwise unchanged.
Server compilation of the repaired module and universe inspection passed with
no errors or unexpected warnings. All lines in the module are at most 100
characters. The worker report above remains as the record of the first pass;
its old module path and implicit-universe description are superseded here.

## Reviewer fix (R-fcl1024, stage 2)

1. Product decomposition restated in the shared form of K1 3d7845984 / M1 c8ddf5893:
   `∃ (t : ℕ) (A : Fin t → Type v)` with `CommRing`, `Algebra R`, `IsLocalRing` instance
   families and `Nonempty (S ≃ₐ[R] ∀ i, A i)`, replacing the `CommRingCat` family over an
   arbitrary `Fintype ι` with a bare `≃+*`; the factors are the R-algebras (S_q)^ of step 4.
   The duplicated local-ring data (a `∀ i, IsLocalRing` conjunct plus a separate
   `∃ h : IsLocalRing` witness for completeness) is now one instance family.
2. Domain clause: `∃! M, M.IsPrime ∧ comap M = m` did not name n. It now says literally that
   the maximal ideal n of S lies over m and every prime over m equals n.
