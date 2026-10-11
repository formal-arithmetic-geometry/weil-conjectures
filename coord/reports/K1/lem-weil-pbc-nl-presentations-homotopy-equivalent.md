## Worker report

The module `Sheaf.RingTheory.PresentationsHomotopyEquivalent` states
`Algebra.Extension.presentations_homotopy_equivalent`. Its only proof is `sorry`;
no definitions or proofs were added. The item copy changes only `lean`.

Source read: Stacks Project, Algebra, Tags 00S0 and 00S1, presentation definition,
naive cotangent differential, and the whole proof of Lemma `lemma-NL-homotopy`.
The repository's untracked literature checkout is absent on this machine. The same
Stacks source is available at `/home/ubuntu/c1-stacks-review/algebra.tex`, and its
lines 35178–35392 were read directly. The specialization is R = R', S = S',
with identity base and quotient maps, exactly as the node states.

Hypothesis and clause correspondence:

| Node | Lean rendering |
| --- | --- |
| R commutative; S a commutative R-algebra | `{R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]` |
| Arbitrary variable sets T,U | `{T : Type w} {U : Type w'}`, with independent, explicitly declared universes |
| P = R[x_t], P' = R[x'_u] | `MvPolynomial T R`, `MvPolynomial U R` in the domains of α,α' |
| Surjective R-algebra homomorphisms α,α' | `α`, `α' : ... →ₐ[R] S`, `hα`, `hα' : Function.Surjective ...` |
| I = ker α, I' = ker α' | `P := ofSurjective α hα`, `P' := ofSurjective α' hα'`; `P.ker`, `P'.ker` are kernels of the corresponding algebra maps, definitionally α,α' |
| I/I² and I'/I'² as S-modules | `P.Cotangent`, `P'.Cotangent`: type synonyms for the ideal cotangents; `Cotangent.module` supplies the quotient scalar action through S, using a section of α. The action is independent of the chosen section modulo I². |
| Targets S tensor_P Ω[P/R], and the primed target | `P.CotangentSpace`, `P'.CotangentSpace`, definitionally those tensor products, with `KaehlerDifferential` |
| Differentials are well defined and S-linear | Existing `P.cotangentComplex`, `P'.cotangentComplex` have types `... →ₗ[S] ...`. No extra hypothesis is used to supply either map. |
| Differential sends f mod I² to 1 tensor df | First `∀ f : P.ker` equation uses `Cotangent.mk f` and `KaehlerDifferential.D R P.Ring f`; second equation is the primed counterpart. These specify the maps on all conormal classes because `Cotangent.mk_surjective` holds. |
| Lifts φ and ψ exist | `Nonempty (P.Hom P') ∧ Nonempty (P'.Hom P)` |
| Any R-algebra lift φ with α'φ = α, and any ψ with αψ = α' | `∀ (φ : P.Hom P') (ψ : P'.Hom P)`. `Hom` bundles exactly these two commuting squares, with identity maps on R and S. `Hom.toAlgHom` gives the R-algebra map, and `Hom.ofAlgHom` accepts every R-algebra map satisfying the indicated equality; no choice of lift is excluded. |
| Four induced S-linear maps φ₁,φ₀,ψ₁,ψ₀ | Four `let` bindings to `Cotangent.map` and `CotangentSpace.map`. Their types are the exact S-linear maps in the node. |
| φ₁(f mod I²) = φ(f) mod I'² (and ψ₁ likewise) | This is the existing definition `Cotangent.map`, with formula `Cotangent.map_mk`. |
| φ₀(s tensor dp) = s tensor dφ(p) (and ψ₀ likewise) | This is the existing definition `CotangentSpace.map`, with formula `CotangentSpace.map_tmul`, specialized to identity on S. |
| S-linear h,h' with the displayed domains | `∃ (h : P.CotangentSpace →ₗ[S] P.Cotangent) (h' : P'.CotangentSpace →ₗ[S] P'.Cotangent)` |
| d_α' φ₁ = φ₀ d_α | First equation under the existential |
| d_α ψ₁ = ψ₀ d_α' | Second equation under the existential |
| id - ψ₁φ₁ = h d_α | Third equation under the existential |
| id - ψ₀φ₀ = d_α h | Fourth equation under the existential |
| id - φ₁ψ₁ = h' d_α' | Fifth equation under the existential |
| id - φ₀ψ₀ = d_α' h' | Sixth equation under the existential |

The four maps are fixed to the induced maps rather than existentially quantified:
the node's final 'moreover' permits those exact choices for every lift. Together
with existence of both lifts, the universal homotopy conclusion entails the
initial existential conclusion. No strengthening or weakening results. The
well-definedness, scalar structures, and induced-map formulas already hold by
the Mathlib definitions; they are not assumed as additional hypotheses.

Dependency declarations read and used:

- `def-weil-pbc-mv-polynomial-ring` is a Mathlib leaf with recorded declarations
  `MvPolynomial`, `MvPolynomial.aeval`, `MvPolynomial.algHom_ext`, in
  `Mathlib.Algebra.MvPolynomial.Basic` / `Mathlib.Algebra.MvPolynomial.Eval`.
  Read their definitions, signatures and docstrings. The statement uses
  `MvPolynomial`; the proof docstring records the universal-property argument.
- `def-weil-pbc-kahler-differentials` is a Mathlib leaf with declaration
  `KaehlerDifferential`, in `Mathlib.RingTheory.Kaehler.Basic`. Read its definition,
  universal derivation `KaehlerDifferential.D`, and
  `KaehlerDifferential.linearMapEquivDerivation`. The two differential formulas
  use D, and `CotangentSpace` uses this same module of differentials.
- Existing machinery read: `Algebra.Extension.ofSurjective`, `ker`, `Cotangent`,
  `Cotangent.module`, `Cotangent.mk`, `Hom`, `Hom.toAlgHom`, `Hom.ofAlgHom`,
  `Cotangent.map`, and `Cotangent.map_mk` in `Mathlib.RingTheory.Extension.Basic`;
  `CotangentSpace`, `cotangentComplex`, `cotangentComplex_mk`,
  `CotangentSpace.map`, `CotangentSpace.map_tmul`, and its chain-map identity in
  `Mathlib.RingTheory.Extension.Cotangent.Basic`.
  The single import of that last module supplies all these declarations and
  both statement dependencies transitively; no private copy was created.

Edge cases checked against the source and definitions:

- Empty T or U: permitted, with no finiteness, nonemptiness, or decidable-equality
  binder. A surjection from a zero-variable polynomial ring is still a valid presentation.
- Infinite variable sets, including different universes: retained by independent w,w'.
- Zero ring R or S: permitted by CommRing; there is no Nontrivial hypothesis.
  Existence of α restricts possible zero-base cases exactly as in the node.
- Identity presentations and zero kernel: the conormal term is zero; the
  equations remain valid with the zero homotopy.
- Arbitrary characteristic and nonreduced rings: no characteristic or reducedness
  condition was introduced; the kernel-square construction is general.
- Homotopy sign: the equations use id minus the composite, matching the node.
  In stage 3 use `(Hom.id P).sub (ψ.comp φ)` and the primed counterpart, in that
  order (the stage-1 candidate's suggested reversed order would give the opposite sign).

Searches made (msearch commands used group K1 and this item's id):

- `leanfinder`: "naive cotangent complexes of two polynomial presentations of the
  same algebra are homotopy equivalent". Eight hits: submersive-presentation
  conormal equivalences, composite cotangent-space equivalences, quotient
  differential modules, H1 equivalences. None packages this full statement.
- `loogle`: `Algebra.Extension.Hom.sub`. Five hits: `Hom.sub`, `sub_one_tmul`,
  `sub_tmul`, and the two `map_sub_map` equations. These give the comparison
  homotopy, not the full existential/universal homotopy-equivalence statement.
- `grep` via msearch: `homotopy|map_sub_map` in `RingTheory/Extension`.
  Three hits, at Cotangent/Basic.lean lines 290,311,394. No packaged theorem.
- `leansearch`: "naive cotangent complexes of two polynomial presentations are
  homotopy equivalent". Unavailable: Internal Server Error; no absence verdict
  is drawn from this failed service.
- `rg` of `homotopy|cotangentComplex` in upstream WeilConjectures/RingTheory:
  unrelated Amitsur contracting homotopies.
- `rg` of this item's id and `cotangentComplex|presentations.*homotopy` in
  upstream WeilConjectures and repository lean/Sheaf: local Jacobian and
  symmetric-algebra cotangent statements, and a docstring referring to this
  still-unstated item. No existing full declaration.
- `grep -rn` of this item's id in upstream WeilConjectures: no matches.
- `rg` of `presentations_homotopy_equivalent` in Mathlib, upstream
  WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json: no name collision.

No missing notions, unusable dependency records, statement corrections, or
STATEMENT-DISPUTED issues were found. No additional node or dependency module
was necessary. The declaration docstring carries all five proof steps and their
DAG dependencies; the theorem is intentionally left unproved for stage 3.

Validation: `scompile.py K1 lem-weil-pbc-nl-presentations-homotopy-equivalent
<module>` compiled the 80-line module in 1.8 seconds, exit code 0, with no
warnings. All variables and universes are explicitly bound. Every Lean line is
at most 100 characters. The second reading is left for the independent reader.

## Second reading by K1

I reread the node statement, its Stacks source (Algebra, Tags 00S0 and 00S1),
and the complete Lean declaration. The correspondence is as follows.

- The node's commutative rings and common algebra structure are rendered by
  `{R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]`.
- Its arbitrary variable sets are `{T : Type w} {U : Type w'}`; no finiteness,
  nonemptiness, decidable equality, or universe restriction is added.
- Its polynomial presentations and surjections are the two maps
  `α : MvPolynomial T R →ₐ[R] S`, `α' : MvPolynomial U R →ₐ[R] S`, with
  `hα` and `hα' : Function.Surjective`; `P` and `P'` are exactly
  `ofSurjective α hα` and `ofSurjective α' hα'`.
- The conormal modules `I/I²` and `I'/I'²` are `P.Cotangent` and
  `P'.Cotangent`, and the two targets `S ⊗ₚ Ω` are `P.CotangentSpace` and
  `P'.CotangentSpace`, using the canonical scalar actions from
  `Mathlib.RingTheory.Extension`.
- The two displayed formulas for the differentials are the first two universal
  conjuncts, using `P.cotangentComplex (Cotangent.mk f)` and
  `KaehlerDifferential.D`; thus they assert the stated well-defined maps on all
  conormal classes.
- Existence of lifts in both directions is exactly
  `Nonempty (P.Hom P') ∧ Nonempty (P'.Hom P)`. For every pair of such lifts,
  the four induced maps are fixed by the `let` bindings to `Cotangent.map` and
  `CotangentSpace.map`.
- The existential `h,h'` has precisely the two chain-map equations and the four
  displayed homotopy identities, with the same domains, composition order, and
  `id - composite` signs as the node. The universal quantifier over all lifts
  implements the node's “may be taken ... by any homomorphism” clause.

The empty variable sets, zero rings, zero kernels, arbitrary characteristics,
nonreduced rings, and infinite sets remain admitted by these binders. No
Noetherian, nontrivial, reduced, or characteristic hypothesis is present. The
identity and zero-kernel cases use the existing zero conormal constructions.

I searched Mathlib, `WeilConjectures`, `lean/Sheaf`, and the DAG for
`presentations_homotopy_equivalent`, cotangent homotopy, and equivalent names;
only the component maps and `map_sub_map` lemmas exist, so this declaration is
not a duplicate. The recorded polynomial and Kähler differential dependencies
are the declarations used by the statement and proof documentation. No missing
notion or unusable dependency was found, and no statement correction was needed.

The only issue found was procedural: the worker report had not yet contained an
independent second-reading section. I added this section; the Lean statement
itself required no change. The module compiles cleanly with `scompile.py`, with
only its intentional theorem `sorry` and no warnings.

## Reviewer fix (R-nph1155)

The `let P`, `let P'` and the four `let φ₁ φ₀ ψ₁ ψ₀` binders of the signature were replaced by the
explicit terms `ofSurjective α hα`, `ofSurjective α' hα'`, `Cotangent.map φ`,
`CotangentSpace.map φ`, `Cotangent.map ψ`, `CotangentSpace.map ψ` (brief: `let` binders in a
statement elaborate as `have`, so stage 3 cannot unfold them; the landed sibling
ConormalModulePrincipalLocalization writes `ofSurjective α hα` explicitly). The mathematics is
unchanged; the docstring names the abbreviations. Recompiled clean (no warnings).
