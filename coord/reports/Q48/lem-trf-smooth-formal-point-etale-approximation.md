## Worker report

The module `Sheaf.RingTheory.SmoothFormalPointEtaleApproximation` states
`AlgebraicGeometry.smooth_formal_point_etale_approximation`, with the entire proof
`sorry`. It introduces no definitions. The node's mathematical statement and proof
are unchanged. Its `stmt_deps` gains the already landed node
`lem-weil-pbc-fs-adic-completion-map-local`, whose recorded upstream theorem
supplies the coordinatewise completion map appearing in the statement. This uses
the standing permission for statement dependencies to gain landed nodes.

Sources read: `literature/stacks-project/smoothing.tex`, Tag 07QZ,
`theorem-approximation-property-variant`, including the smooth-factorization
paragraph; `literature/stacks-project/more-algebra.tex`, Tag 07M7,
`lemma-lift-section-smooth-morphism`; and the Mathlib theorem tagged 05GG (2).
The source proof uses 07M7 at the maximal ideal after its polynomial substitution;
the node's stated precision-N refinement applies that same lemma directly to
`m^N`. Tag 07M7 allows arbitrary ideals and needs neither henselianity nor a
G-ring assumption. This refinement is consistent with all four node proof steps.

Every hypothesis and clause is rendered as follows. In this table `m` denotes
`IsLocalRing.maximalIdeal R` and `T` denotes the actual type
`Localization.AtPrime q.asIdeal`; these are explanatory abbreviations only,
not additional Lean declarations or file-local notation.

| Node text | Lean rendering |
| --- | --- |
| Commutative Noetherian local ring R | `(R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]` |
| Commutative R-algebra B | `(B : Type u) [CommRing B] [Algebra R B]` |
| Spec B → Spec R smooth | `hB : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R B)))` |
| Maximal-ideal completion of R | `AdicCompletion (IsLocalRing.maximalIdeal R) R` |
| R-algebra map w to that completion | `w : B →ₐ[R] AdicCompletion m R` |
| Integer N ≥ 1 | `(N : ℕ) (hN : 1 ≤ N)`; natural numbers with this bound are exactly the stated positive integers |
| Coordinate projection π_N | `AdicCompletion.evalₐ m N` |
| Étale R-algebra E | `∃ E : CommAlgCat.{u} R, Etale (Spec.map (CommRingCat.ofHom (algebraMap R E))) ∧ ...` |
| Structural quotient map α is an isomorphism | `α : R ⧸ m ^ N →ₐ[R] E ⧸ ((m ^ N).map (algebraMap R E))`, with `Function.Bijective α`; any R-algebra map from this quotient must be structural |
| R-algebra homomorphism t | `∃ t : B →ₐ[R] E, ...` |
| q_N t = α π_N w | Equality for every `z : B`, with `Ideal.Quotient.mk` on the left and `α (AdicCompletion.evalₐ m N (w z))` on the right |
| q = mE | `q : PrimeSpectrum E` with `q.asIdeal = m.map (algebraMap R E)`; the equality fixes the prime rather than allowing an arbitrary one |
| q maximal and contracting to m | `q.asIdeal.IsMaximal` and `q.asIdeal.comap (algebraMap R E) = m` |
| Structural R/m → κ(q) is an isomorphism | `∃ ρ : R ⧸ m ≃+* q.asIdeal.ResidueField`, with `ρ (Ideal.Quotient.mk m r) = algebraMap E q.asIdeal.ResidueField (algebraMap R E r)` for every r; the equation fixes the structural map uniquely |
| T = E_q, local | The actual `Localization.AtPrime q.asIdeal`, with its Mathlib local-ring instance |
| n = qT = mT | Both displayed equalities identifying `IsLocalRing.maximalIdeal T` with `q.asIdeal.map (algebraMap E T)` and with `m.map ((algebraMap E T).comp (algebraMap R E))` |
| Local structure map λ : R → T | The explicit composite `(algebraMap E T).comp (algebraMap R E)` and existential proof `hlocal : IsLocalHom` for it; this makes the locality already implicit in the node's local-map description available to the completion construction |
| Coordinatewise induced completion map λ̂ | `Classical.choose (@RingHom.exists_adicCompletion_map_of_local R T ... λ hlocal)`; the recorded theorem pins every quotient coordinate, so the resulting map is unique by `AdicCompletion.ext_evalₐ` and is not an arbitrary chosen map |
| Completion map ι_T | `AdicCompletion.of (IsLocalRing.maximalIdeal T) T` |
| t(z)/1 | `algebraMap E T (t z)` |
| Congruence for every z ∈ B | `∀ z : B`, the exact difference `λ̂ (w z) - ι_T (t(z)/1)` belongs to `((IsLocalRing.maximalIdeal T) ^ N).map (algebraMap T (AdicCompletion (IsLocalRing.maximalIdeal T) T))` |

The quotient ideal is the image of `m^N`, hence is exactly `m^N E`; the final
ideal is the extension of `n^N` to the completion, not a statement merely about
one coordinate. No isomorphism of completed rings is assumed or asserted. The
same universe for the two input rings is the existing affine smooth/étale API
convention: any two ring types can be considered at their common maximum
universe. No size restriction on test rings occurs.

Dependency declarations used, with signatures and docstrings inspected:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and
  `isNoetherianRing_iff_ideal_fg` (every ideal finitely generated).
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`,
  its commutative-ring and algebra instances, `AdicCompletion.evalₐ`,
  `AdicCompletion.of`, and `AdicCompletion.ext_evalₐ`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`,
  its local-ring instance and the canonical localization algebra map.
- `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Ideal.ResidueField`,
  defined as the residue field of the actual prime localization.
- `WeilConjectures.RingTheory.CompletionMapForLocalHom`:
  `RingHom.exists_adicCompletion_map_of_local`, the additional landed dependency.
- Proof-only import `Mathlib.RingTheory.AdicCompletion.Completeness`:
  `AdicCompletion.pow_smul_top_eq_ker_eval`, matching the completion-mod-power
  node's Mathlib record.
- Proof-only import `WeilConjectures.AlgebraicGeometry.SmoothSectionEtaleLift`:
  `AlgebraicGeometry.exists_etale_lift_of_smooth`. The recorded Sheaf module and
  this upstream module declare the same theorem with the same signature and
  proof; the upstream module is imported, following the launcher's explicit
  instruction to prefer upstream when a library-side duplicate exists.

Edge cases checked before writing: N=1 recovers the section-lifting paragraph
of 07QZ; R a field has m=0 and a genuine map w into R, so E=R realizes the
statement; for Artinian R with m^N=0 the lift agrees exactly at that quotient;
R=k[[x]] and B=R[y] permit arbitrary formal values of y and prescribed finite
precision. The zero input ring R is excluded by the usual nontriviality built
into `IsLocalRing`, exactly as for a local ring with a maximal ideal. B=0 over
nonzero R has no unital map w to the nonzero completion, so it introduces no
false case. No separatedness or injectivity of R → its completion is required.
For B=R and the canonical w, E=R gives a witness. The maximality and contraction
conditions ensure T is a genuine nonzero local ring.

Searches made with the prescribed msearch wrapper:

- LeanFinder: `Etale approximation of a smooth algebra homomorphism to the
  completion of a Noetherian local ring at prescribed maximal ideal power`.
  Eight hits: standard-smooth polynomial étale charts, standard-étale
  presentations and lifts, and the étale locus. None states this approximation.
- Loogle: `Algebra.Smooth, Algebra.Etale`. Two hits,
  `Algebra.Etale.instSmooth` and
  `Algebra.Etale.iff_formallyUnramified_and_smooth`; neither constructs a lift.
- Mathlib grep: `etale.*(approximation|section)|smooth.*(approximation|section)`
  in `RingTheory`. Two hits in `Smooth/Flat.lean` and `Smooth/Basic.lean`, about
  formal-smoothness sections, not pointed étale approximation.
- LeanSearch: `A smooth algebra map to the completion of a local ring admits
  an etale approximation modulo a maximal ideal power`. Eight hits concerning
  formal smoothness, completion lifting into a supplied target and basic étale
  properties; none produces E with the stated structural isomorphisms.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `etale.*approximation|exists_etale_lift|smooth_formal|adicCompletionMap`;
  found the generic smooth-section theorem, the already landed local completion
  map, and downstream approximation results. The latter require G-rings or
  geometric input and do not state this smooth-algebra lemma. The principal
  completion map `AdicCompletion.principalRingMap` has a different interface and
  is not used for general maximal ideals.
- ID search in `lean/WeilConjectures` and full-name search in both libraries
  and `dag/lean_names_upstream.json` found no existing statement of this item.

Validation: the prescribed scompile.py compiled the sandbox and named module
successfully (7.3 s and 2.3 s), with no diagnostics. The first compile caught the
identifier `hλ` being tokenized at the lambda symbol; it was renamed `hlocal`.
No mathematical statement fault or dispute was found. No new nodes or dependency
repair modules are supplied.

## Second reading by Q48

Reread the node and the complete module after compilation, clause by clause.
The smoothness and étaleness assumptions use the exact recorded scheme-morphism
predicates; w is an R-algebra map, not a bare ring map. α has no freedom because
it is an R-algebra map out of a quotient; its bijectivity expresses precisely
the required structural isomorphism. The lifting equality uses the actual N-th
projection. The prime q is forced to be mE, is maximal, and contracts to m.
The equation on ρ ensures its isomorphism is the structural residue-field map,
not just an abstract equivalence of two fields. T is the actual localization;
both equalities for n are present. The completion map's theorem characterizes
all its coordinates, ruling out an arbitrary map. The congruence holds for
every element of B and uses the extension of n^N in the target completion.
Positive precision and all Noetherian/local hypotheses are present, and neither
a G-ring nor henselian hypothesis was introduced. The proof docstring reproduces
the four node steps. No mismatch remained and no further change was made.
This second pass was performed in this worker session, as the dispatcher
explicitly prohibits starting other agents; independent review is by the
maintainer after delivery.
