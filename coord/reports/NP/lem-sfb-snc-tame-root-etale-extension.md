## Worker report

The module `Sheaf.AlgebraicGeometry.SNCTameRootEtaleExtension` states
`AlgebraicGeometry.ProEtale.SNCTameExtension.exists_finite_root_etale_extension`.
It reuses `AlgebraicGeometry.ProEtale.tameRootAlgebra` and
`Algebra.StrictHenselizationPresentationIn`, and defines only the canonical auxiliary
maps needed to render the node: `active` filters the parameters in a prime, `coefficient`
is the localization-to-strict-local algebra map, `localParameters` transports active
parameters, `localProjection` is the spectrum map of the canonical root-algebra map,
`puncture` is `Spec (B[1/(∏ t_i)]) → Spec B`, `localPuncture` is its canonical pullback
projection, and `finiteProjection` is the simultaneous literal polynomial-root quotient.
Every auxiliary definition has real data; none uses `sorry`.

The theorem renders the node hypothesis by hypothesis as follows. `p : ℕ` with
`[Fact p.Prime]` is the positive characteristic prime; `k` with `[Field k]` and
`[CharP k p]` is the field of characteristic `p`. `B` is a commutative ring and
`b : Spec B ⟶ Spec k` has `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated`; the
regularity hypothesis is `IsRegularScheme (Spec B)`. The finite family is `r : ℕ` and
`t : Fin r → B`. `D` is the stated strict normal crossings boundary, with the exact
product equality to `Ideal.span {Γ(Spec B)⁻¹(∏ i, t i)}`. The regular-system-of-parameters
condition is written for every prime `q : PrimeSpectrum B`, including local
Noetherianity, a list of parameters, and the active transported list as a `Sublist`.
The finite étale input is a scheme `P`, its map `π` to the puncture, and typeclass
hypotheses `[IsFinite π] [Etale π]`.

The local splitting clause quantifies every prime `q`, every residue separable closure
`K` of the residue field of `Localization.AtPrime q.asIdeal`, every strict-local algebra
`H`, and every `Algebra.StrictHenselizationPresentationIn`. It asserts a finite
number `d`, an isomorphism from the pullback of `π` to the disjoint union of copies of
the local root tower, and the exact equation saying its map to the base is the pullback
projection. The conclusion gives `n > 0` and `n.Coprime p`, a scheme `Z` over the finite
simultaneous root quotient, finite and étale structure on `ζ`, and an isomorphism after
punctured base change with the pullback of `P`; its projection equation is included.
The `Fin r` and `Fin (active t q).length` forms include `r = 0`, and the disjoint union
allows the empty cover (`d = 0`). No connectedness, Galois action, degree invertibility,
residual-cover condition, or root-of-unity choice is added.

Statement dependencies used: `def-weil-regular-scheme` via
`AlgebraicGeometry.IsRegularScheme` (`Sheaf.AlgebraicGeometry.IsRegularScheme`),
`def-weil-pbc-scheme-conventions` via the Mathlib morphism classes,
`def-trf-strict-normal-crossings-boundary` via
`AlgebraicGeometry.IsStrictNormalCrossingsBoundary`
(`Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`),
`def-weil-pbc-regular-system-of-parameters` via
`IsLocalRing.IsRegularSystemOfParameters`
(`WeilConjectures.RingTheory.IsRegularSystemOfParameters`),
`def-weil-pbc-finite-etale-category` via `IsFinite` and `Etale`, and
`def-sc-ring-strict-henselization` via
`Algebra.StrictHenselizationPresentationIn`
(`Sheaf.RingTheory.StrictHenselizationPresentationIn`). The added dependency
`def-sfb-strict-local-kummer-tame-module` supplies
`AlgebraicGeometry.ProEtale.TameRootOrder` and `tameRootAlgebra` from
`Sheaf.Paper.StrictLocalKummerTameModule`. Proof-dependency imports and declarations are
recorded in the theorem docstring: they are the stage-1 finite-root regularity,
normalization, descent, and generic-full-faithfulness inputs, with Mathlib leaves used
where recorded.

Edge cases checked against the statement and its proof: `r = 0` (empty product and
identity puncture), `n = 1`, empty `P` (the disjoint-union index `d = 0`), zero/empty
root quotients, disconnected or reducible boundary components, points off the boundary
(the active list is empty), and inactive labels (their derivatives are units). The
hypotheses do not require a connected scheme, Galois cover, invertible degree, chosen
roots of unity, or residual splitting beyond the displayed strict-local tower clause.

Source checked directly: ILO IX Proposition 2.1 and its proof on printed pp.133–134
(PDF pp.139–140), including its strict-local parameter-root presentation and
étale-locality statement. The node itself supplies the tower-splitting hypothesis
and its stage-1 split provides the quasi-compact common-level descent argument.

Searches for an existing declaration: `msearch.py leanfinder` with the finite tame-cover
extension query returned only generic étale-locality, standard-étale, and unramified
lemmas; `msearch.py loogle '"Etale", "AdjoinRoot"'` returned only
`StandardEtalePair.equivAwayAdjoinRoot`; `msearch.py grep '(tame|Abhyankar|normal.?crossing).*(etale|root)|(etale|root).*(Abhyankar|normal.?crossing)'`
returned zero hits. `msearch.py leansearch` with the finite-etale SNC extension
query returned only generic étale composition, loci, and field decomposition results. `rg` over `lean/Sheaf` and `lean/WeilConjectures` found no declaration
for this node. The existing root-tower declarations were found in
`Sheaf.Paper.StrictLocalKummerTameModule`; they are reused rather than copied.
No `STATEMENT-DISPUTED` issue was found.

## Worker self-check

I reread the node and the module. The characteristic, finite-type separated regular affine
base data, SNC product boundary, primewise parameter sublist, finite étale punctured cover,
and all strict-local splitting quantifiers are present. The conclusion has exactly one
common positive prime-to-`p` level, a finite étale cover over its simultaneous root
quotient, and the required punctured isomorphism with its projection equation. The
auxiliary maps are canonical constructions used to spell those objects, and the
statement does not impose connectedness, Galois, degree, or root-of-unity hypotheses.
The empty tuple, empty cover, reducible boundary, inactive labels, and order one are
represented explicitly. No mismatch was found.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
