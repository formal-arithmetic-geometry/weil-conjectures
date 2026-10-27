## Worker report

The module `Sheaf.RingTheory.EquivariantRelativeCoordinateLift` states
`MvPowerSeries.exists_equivariant_relative_coordinate_lift`, with exactly one postponed
proof (`sorry`) and no definitions, axioms, or proved theorems. The node changes only in
`lean`. No statement correction, new nodes, or dependency modules are required.

I read the current node, every statement dependency's statement and recorded interface,
and the actual source declarations and docstrings. I read ILO, Travaux de Gabber,
VIII Lemma 5.5.2, proof, printed p.128 (the two eigenparameter families, their common
prefix, the Cohen surjection, and weighted averaging), and Stacks `more-algebra.tex`,
Tag 07NM, `lemma-quotient-power-series-ring-over-Cohen`, clause (3) and proof. I also
read the current blueprint ancestor `lem-per-artin-gabber-affine-curve.proof.md`, step 3.
The docstring gives the accepted five-step DAG proof, including why the relative
cotangent space is I/(pI+I^2) and why lifts must be chosen in I. The primed character
is used for averaging, as in the reviewed split (ILO's unprimed character is a typo).

The previous worker's ending concerned a stale stage-1 split assignment. The live
item is split, has no `lean` record, and is queued for stage 2. The explicit stage
handoff at the start of `coord/brief-stage2.md` permits recording this Lean statement
without reopening that accepted split. There is no released repair note for the item.

Hypothesis correspondence:

| Node hypothesis | Lean rendering |
| --- | --- |
| Cohen coefficient ring C of residue characteristic p > 0 | `C : Type u`, `[CommRing C]`, `hC : IsCohenRing p C`. This predicate includes `Nat.Prime p`, the DVR, its maximal ideal `(p)`, and completeness. |
| The local and Noetherian coefficient structures | `[IsLocalRing C] [IsNoetherianRing C]` expose the structures already entailed by the Cohen-ring predicate, so that residue fields, parameter predicates and power-series instances elaborate. They impose no additional mathematical restriction. |
| Residue field k | Use the canonical `IsLocalRing.ResidueField C` as k; a separately named field is unnecessary, since any given identification transports to this field. |
| R = C[[t_1,...,t_d]], d >= 0 | `MvPowerSeries (Fin d) C`, with `d : ℕ`, and `X i` as t_i. |
| H finite abelian of order N | `H : Type v`, `[CommGroup H] [Fintype H]`, with N represented by `Fintype.card H`. Choosing a finite enumeration does not restrict finite groups. |
| N invertible in C | `hN : IsUnit (Fintype.card H : C)`. |
| Unit zeta and zeta^N = 1 | `ζ : Cˣ`, `hζ : ζ ^ Fintype.card H = 1`. Equality in units is equivalent to equality of their values in C. |
| 1-zeta^a invertible for 1 <= a < N | `hsep`, quantified over `a : ℕ` with both bounds explicit. |
| Two families of characters with values in <zeta> | `χ χ' : Fin d → H →* Cˣ`, with `hχ` and `hχ'` placing every value in `Subgroup.zpowers ζ`. This is exactly a homomorphism into that subgroup, expressed using its inclusion into units. |
| H acts on R by automorphisms | `ρ : H →* RingAut (MvPowerSeries (Fin d) C)`. The monoid-homomorphism laws supply the action laws. |
| Continuity on R | `hcontinuous` uses `@Continuous` with both topologies explicitly the maximal ideal's `adicTopology`; there is no arbitrary topology binder or file-local instance. For finite H, continuity of each automorphism is the continuous action for discrete H. |
| C fixed pointwise | `hfixed`, at every `MvPowerSeries.C c`. |
| h(t_i) = chi_i(h)t_i | `heigen`, with scalar expressed by `MvPowerSeries.C (χ i h).val`. |
| A complete Noetherian regular local | `A : Type w`, `[CommRing A] [IsRegularLocalRing A]` and `[IsAdicComplete (IsLocalRing.maximalIdeal A) A]`. Mathlib's regular-local class includes localness and Noetherianity. |
| H acts on A by local ring automorphisms | `α : H →* RingAut A`. A ring automorphism of a local ring automatically preserves its unique maximal ideal; no extra arbitrary local structure or action is substituted. |
| Equivariant local surjective ring map f | `f : MvPowerSeries (Fin d) C →+* A`, `[IsLocalHom f]`, `hfsurj`, and `hf` on every h and r. |
| Identified residue field, inducing the given identification | `residueIdentification : ResidueField C ≃+* ResidueField A`, and `hresidue` equating the residue of `f (C c)` with its image through that identification for every c. |
| z_i = f(t_i) is a regular system of parameters | `hparameters : IsLocalRing.IsRegularSystemOfParameters (List.ofFn (fun i : Fin d ↦ f (X i)))`; z_i is inlined, rather than introduced as independent data. |
| Another regular system z'_i | `z' : Fin d → A` and `hparameters'` for `List.ofFn z'`. |
| h(z'_i) = chi'_i(h)z'_i, character values via C -> A | `heigen'` uses precisely `f (MvPowerSeries.C (χ' i h).val)` as scalar. |
| 0 <= l <= d and z'_i = z_i for i <= l | `l : ℕ`, `hl : l ≤ d`, and `hprefix` for `i.val < l`. Fin indices start at zero, so `< l` is the first l variables. |

Conclusion correspondence, in conjunction order:

1. `∃ t' : Fin d → MvPowerSeries (Fin d) C` supplies all lifted coordinates.
2. Membership in `Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) C))`
   says each lift lies in the variables ideal, not merely in the maximal ideal.
3. `∀ i, f (t' i) = z' i` is the required lift condition.
4. `∀ i, i.val < l → t' i = X i` keeps the common prefix literally fixed.
5. The next equation `ρ h (t' i) = C (χ' i h).val * t' i` is the primed
   eigencharacter condition.
6. `IsRegularSystemOfParameters (C (p : C) :: List.ofFn t')` gives the full ordered
   parameter list p,t'_1,...,t'_d in R.
7. `∃ e : MvPowerSeries (Fin d) C ≃ₐ[C] MvPowerSeries (Fin d) C` is the C-algebra
   isomorphism, with domain variables regarded as s_i and codomain variables as t_i.
   The equation `e (X i) = t' i` gives its values on the source coordinates.
8. `∀ F, e F = subst t' F` identifies the map with Mathlib's actual canonical
   substitution on all series, rather than an arbitrary equivalence with prescribed
   finite coordinate values. Since the lifts are in the variables ideal, their
   constant coefficients vanish, so the finite-variable substitution is admissible.
9. The explicit maximal-ideal-adic `@Continuous ... e` gives continuity.
10. `e (rescale (fun i ↦ (χ' i h).val) F) = ρ h (e F)` is equivariance for every
    group element and every source series. `rescale` is the existing coefficientwise
    diagonal action: it fixes C and sends s_i to chi'_i(h)s_i. Character laws make
    these rescalings an action, with inverses given by h^{-1}.

Dependency declarations used:

- `WeilConjectures.RingTheory.CohenRing`: `IsCohenRing`, full definition read.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `MvPowerSeries.C`,
  `MvPowerSeries.X`, imported publicly through the power-series modules. `Equiv`
  supplies the finite-variable Noetherian instance and `Inverse` the local instance.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete`, the companion of the
  recorded `AdicCompletion` declaration; the node's record explicitly lists both.
  Both definitions and their surrounding variable binders were read. Available
  publicly via `CohenRing`.
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing`, exactly the ring
  clause of `def-weil-regular-scheme`'s preserved `mathlib_match`. Its scheme-only
  recorded declaration `AlgebraicGeometry.IsRegularScheme` is not applicable to the
  ring A; its source was read and no scheme notion is redefined here. The needed
  ring class is public through `IsRegularSystemOfParameters`.
- `WeilConjectures.RingTheory.IsRegularSystemOfParameters`:
  `IsLocalRing.IsRegularSystemOfParameters`, used for all three parameter lists.
- `Mathlib.RingTheory.LocalRing.ResidueField.Defs`: `ResidueField`, `residue`.
- `Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology`: `Ideal.adicTopology`.
- `Mathlib.Algebra.Group.Subgroup.ZPowers.Basic`: `Subgroup.zpowers`.
- `Mathlib.RingTheory.MvPowerSeries.Substitution`: `MvPowerSeries.subst`,
  `MvPowerSeries.rescale`; their definitions and admissibility interface were read.

The already stated proof dependencies are imported privately:
`WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete` with
`MvPowerSeries.power_series_field_cohen_regular_complete`,
`WeilConjectures.RingTheory.PowerSeriesFullCoordinatesCohen` with
`MvPowerSeries.exists_algEquiv_full_parameters_cohen`, and
`Mathlib.RingTheory.LocalRing.Module` with `IsLocalRing.map_mkQ_eq_top`.
The cotangent-dimension dependency is the Mathlib leaf
`IsRegularLocalRing.iff_finrank_cotangentSpace` in the already public
`Mathlib.RingTheory.RegularLocalRing.Defs`. The statements and docstrings of these
proof interfaces were read. No sibling module or additional canonical construction
is needed.

Edge cases checked before writing:

- d=0: all indexed hypotheses are empty, l=0, the variables ideal is zero, and the
  conclusion says [p] is a parameter system of C and the coefficient identity is an
  equivariant isomorphism. The finite-variable formulation includes this case.
- l=0: no prefix condition; all coordinates can be averaged.
- l=d: every coordinate is literally fixed. The eigencharacter agreement follows
  from nonzero parameter classes and unit differences of roots; no equality of
  characters is added as an assumption.
- H trivial, N=1: the separation range is empty and both character families are
  trivial; ordinary relative coordinate lifting remains.
- Repeated characters and a nonfaithful action are allowed; there are no
  distinctness, faithfulness, or algebraicity assumptions on the action.
- Mixed-characteristic ramification is allowed: for C=Z_p and A given by
  C[[t]]/(p-t), f(p) can lie in m_A but need not be zero. The proof uses
  I/(pI+I^2), not A/(p), and the Lean imposes no `CharP A p`.
- Separate universes u,v,w for the coefficient ring, finite group and quotient
  ring exclude no size cases. No test ring or scheme is quantified over a smaller
  independent universe. The zero ring is already excluded by local regularity.

Actual searches run with `msearch.py Q45 lem-per-equivariant-relative-coordinate-lift`:

- LeanFinder: `Equivariant eigenvector regular parameter lifts through a Cohen power
  series quotient fixing a common prefix`. Eight hits, including
  `Module.End.HasUnifEigenvalue.exists_hasUnifEigenvector`, `HasGenEigenvector`,
  and `PreTilt.exists_smodEq_untiltAux`; none states a Cohen quotient coordinate lift.
- Loogle: `"MvPowerSeries", "AlgEquiv"`. Four hits, namely
  `MvPolynomial.toMvPowerSeries_pUnitAlgEquiv` and the three
  `MvPowerSeries.toAdicCompletionAlgEquiv` declarations. These identify a completion,
  not equivariant changes of quotient parameters.
- LeanSearch: `Equivariant eigenvector parameter lifts through a power series
  quotient over a Cohen ring`. Eight hits, including eigenvector identities,
  `PowerSeries.algEquivQuotientWeierstrassDistinguished`, and representation
  coinvariant maps; no match.
- Mathlib grep, subdirectory `RingTheory`:
  `(equivariant|eigenvector|character).*(lift|parameter)|(lift|parameter).*(equivariant|eigenvector)`.
  One irrelevant hit in `Flat/Tensor.lean` mentioning `CharacterModule`.
- A wrapper grep `equivariant.*relative.*coordinate|relative.*coordinate.*lift`
  returned no hit. Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf`
  checked the item id, coordinate/equivariant phrases, and the full proposed
  declaration name. No existing target declaration. The simultaneous Cohen
  rigidification module mentions this item in its proof docstring and supplies
  coordinate witness structures, not this lifting theorem. The same name was
  also checked in `dag/lean_names_upstream.json`.

Validation: the prescribed server `scompile.py` compiled the final module in both
its sandbox and its actual library namespace in 2.7 s and 2.2 s, cleanly. During
preparation an incorrectly named ZPowers import was fixed, and the power-series
`Inverse` module was imported publicly so its local-ring instance is visible in
public signatures. No definition or statement was weakened to address those
import issues. The signature has explicitly bound universes and variables, with
both auto-implicit options disabled; every Lean line has at most 100 characters.

No outstanding node fault or STATEMENT-DISPUTED issue was found. The independent
mathematical review is the maintainer's, as required by the direct-delivery brief.

## Second reading by Q45

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
