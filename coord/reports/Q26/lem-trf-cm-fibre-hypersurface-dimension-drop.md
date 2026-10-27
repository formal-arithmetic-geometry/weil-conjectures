## Worker report

Module: `Sheaf.AlgebraicGeometry.CohenMacaulayFibreHypersurfaceDimensionDrop`.
Declaration: `AlgebraicGeometry.exists_affine_flat_hypersurface_of_fiber_depth`.
It states the entire affine hypersurface existence and fibre-stalk dimension-drop
assertion. The sole postponed proof is this theorem, with the five DAG proof steps
in its docstring. No definitions or helper theorems are introduced. The item changes
only in `lean`; its statement, dependencies and accepted proof split are preserved.

Sources read: Stacks Project `more-morphisms.tex`, lemma-slice-given-element
(Tag 056Y), lemma-slice-once (056Z), and the positive-dimensional paragraph of
lemma-slice-CM (0570). The algebraic conclusion uses the recorded Tag 02JN theorem.
The local source agrees with the node; no correction or disputed statement is needed.

Hypothesis correspondence:

| Node hypothesis | Lean rendering |
| --- | --- |
| Schemes Y and S and morphism g | `{Y S : Scheme.{u}} (g : Y ⟶ S)` |
| g flat | `[Flat g]` |
| g locally of finite presentation | `[LocallyOfFinitePresentation g]` |
| Base point s and point y of the scheme-theoretic fibre | `(s : S) (y : g.fiber s)` |
| y closed in that fibre | `hy : y ∈ closedPoints (g.fiber s)` |
| A is the local ring of that fibre at y | `(g.fiber s).presheaf.stalk y`, used everywhere for A |
| A Noetherian | `[IsNoetherianRing ((g.fiber s).presheaf.stalk y)]` |
| Finite dimension d with dim A = d | `(d : ℕ)` and `hd : ringKrullDim ... = (d : WithBot ℕ∞)` |
| d > 0 | `hdpos : 0 < d` |
| depth(A) at least d | `hdepth : (d : ℕ∞) ≤ IsLocalRing.depth (R := A) A`, with A expanded in the file |

Conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Affine open neighbourhood of the image of y | `∃ (U : Y.Opens) (hU : IsAffineOpen U) (hx : g.fiberι s y ∈ U)` |
| U = Spec B and a in B | `a : Γ(Y, U)`; B is this section ring and `hU.fromSpec : Spec Γ(Y,U) ⟶ Y` is its canonical open immersion |
| Germ h of a | `h : Y.presheaf.stalk (g.fiberι s y)` and `h = Y.presheaf.germ U (g.fiberι s y) hx a` |
| Image hbar of h in A | `hbar : A` and `hbar = (g.fiberι s).stalkMap y h` |
| h in the total-space maximal ideal | Explicit membership in `IsLocalRing.maximalIdeal (Y.presheaf.stalk (g.fiberι s y))` |
| hbar in the fibre maximal ideal | Explicit membership in `IsLocalRing.maximalIdeal A` |
| Multiplication by hbar injective | `Function.Injective (fun z : A ↦ hbar * z)` |
| D is the actual principal quotient Spec(B/(a)) | The domain of i is exactly `Spec (.of (Γ(Y,U) ⧸ Ideal.span {a}))` |
| D embeds in U, then in Y | `i = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))) ≫ hU.fromSpec` |
| D to S flat and locally of finite presentation | `Flat (i ≫ g) ∧ LocallyOfFinitePresentation (i ≫ g)` |
| A closed point yD in Ds mapping to y | `∃ (yD : (i ≫ g).fiber s) (hyD : ((i ≫ g).fiberι s ≫ i) yD = g.fiberι s y)`, followed by `yD ∈ closedPoints ((i ≫ g).fiber s)` |
| Local ring of Ds at yD isomorphic to A/(hbar) | `∃ e : ((i ≫ g).fiber s).presheaf.stalk yD ≃+* (A ⧸ Ideal.span {hbar})` |
| Isomorphism compatible with maps from O(Y,x) | For every original germ r, applying the canonical map to the Ds stalk and then e equals `Ideal.Quotient.mk (Ideal.span {hbar}) ((g.fiberι s).stalkMap y r)` |
| New fibre stalk Noetherian | Explicit `IsNoetherianRing` conclusion on that stalk |
| New fibre stalk dimension d-1 | Explicit `ringKrullDim ... = ((d - 1 : ℕ) : WithBot ℕ∞)` |
| New fibre stalk depth at least d-1 | Explicit `((d - 1 : ℕ) : ℕ∞) ≤ IsLocalRing.depth ...` |

The existential names h, hbar and i are each constrained to their actual canonical
values by equalities. In particular i cannot be chosen as an arbitrary morphism.
The first factor of its displayed definition is the actual quotient closed immersion;
the second is the canonical affine-open immersion. The total-space point equality
hyD means precisely that yD maps to y on fibres: the universal property gives that
fibre map, and `g.fiberι s` is an embedding, hence injective. No arbitrary fibre map is
assumed. `stalkCongr (.of_eq hyD)` identifies the source of the composite stalk map
with the original total-space stalk. Its inverse is used, so the compatibility
formula has the correct variance. A ring equivalence of local rings automatically
preserves maximal ideals, so `≃+*` expresses the stated local-ring isomorphism.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, scheme morphisms,
  `AlgebraicGeometry.Spec`, `Spec.map`, and `Scheme.Hom.stalkMap`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `Scheme.Hom.fiberι`;
  `fiberHomeo` and the embedding of `fiberι` justify the point interpretation.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.Topology.JacobsonSpace`: `closedPoints`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `WeilConjectures.RingTheory.Depth`: `Ideal.depth`, `IsLocalRing.depth`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffineOpen.fromSpec` and its
  open-immersion instance; the affine-open stalk localization and germ formulas
  are the recorded Mathlib matches for the proof dependency.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, as realized by the quotient spectrum map.

Proof-dependency imports are non-public, following the DAG plan:

- `Sheaf.AlgebraicGeometry.FibreStalkQuotient`:
  `Scheme.Hom.fiberStalkMap_surjective_ker_quotientEquiv` and `fiberStalkMap`.
- `Sheaf.AlgebraicGeometry.Morphisms.FibreRegularElementFlatHypersurface`:
  `AlgebraicGeometry.exists_affine_flat_hypersurface_of_fiber_regular`.
- `WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage`:
  `AlgebraicGeometry.closedSubscheme_baseChange_ideal_image`.
- `Mathlib.RingTheory.Localization.Ideal` and its imports supply the recorded
  quotient-localization instance, `IsLocalization.algEquiv`, and
  `Ideal.map_primeCompl_comap_of_surjective`.
- `WeilConjectures.RingTheory.DepthQuotientNonzerodivisor`:
  `IsLocalRing.depth_quotient_nonzerodivisor`.
- `RingTheory.Sequence.IsRegular`, from the regular-sequence Mathlib module
  publicly imported by the recorded depth module, is the regular-sequence
  proof dependency. No private copy of depth or regularity is used.

Searches for an existing statement:

- `msearch.py ... leanfinder`: “A flat hypersurface through a closed Cohen Macaulay
  fibre point of positive dimension is flat locally finitely presented and has local
  fibre dimension one less”. Eight hits about standard smoothness, flatness and
  going-down; none states this existence assertion.
- `msearch.py ... loogle`: `"Flat", "depth"`; zero hits.
- `msearch.py ... grep`:
  `(CohenMacaulay|depth).*(hypersurface|slice)|hypersurface.*(flat|dimension)`;
  zero hits in Mathlib.
- `msearch.py ... leansearch`: “A flat hypersurface slice through a Cohen Macaulay
  closed fibre point lowers the local dimension by one”. Eight hits, including
  `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors`
  and `Flat.stalkMap`. These cover component conclusions, not the relative existence
  statement with a compatible fibre-stalk isomorphism.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`: hypersurface, fibre dimension drop,
  and the exact item id. Found the existing regular-element hypersurface theorem,
  groupoid slices and downstream closed-fibre regular slices. None is this theorem.
  The downstream regular-slice module mentions this node only in its proof plan.
- Searched the DAG's upstream-name index and both source trees for
  `exists_affine_flat_hypersurface_of_fiber_depth`; no existing declaration.
- Searched both project trees and Mathlib algebraic geometry for existing
  principal-hypersurface inclusion definitions. None found; no new definition is
  needed because the canonical quotient map is written directly in the statement.

Edge cases checked before writing:

- Empty source or empty fibre cannot supply y. No nonemptiness is added separately.
- d = 0 is explicitly outside the node; `0 < d` matches this. At d = 1 the conclusion
  is a nonzero local ring of dimension zero and the depth bound is zero.
- Infinite dimension is excluded by the hypothesis equating dimension to a natural
  number; negative infinity would be the zero ring, impossible for a scheme stalk.
- The fibre element cannot be a unit because it belongs to its maximal ideal. It
  cannot be zero because multiplication is injective on the nonzero local ring.
  The quotient is therefore a proper local quotient, including in dimension one.
- The base and total space need not be Noetherian. Only the specified fibre stalk
  has the Noetherian hypothesis; the point s need not be closed.
- No characteristic restriction or field choice is introduced. The scheme universe
  u is arbitrary; the affine ring and its quotient stay in that same universe.

Validation: the delivered module compiled cleanly with the prescribed `scompile.py`
server checks, both as the sandbox module and at its intended library module name.
No errors or non-sorry warnings occurred. Every universe and binder is explicit;
`autoImplicit` and `relaxedAutoImplicit` are both disabled.

## Second reading by Q26

Worker self-check with the node and final Lean file open; the independent maintainer
reading remains part of the delivery review, as the dispatch brief specifies. No
second agent was started. The correspondence tables above cover every hypothesis
and conclusion, including both maximal-ideal memberships, the actual quotient
spectrum, closedness in Ds, and compatibility for every germ of the total-space
stalk. The direction of `stalkCongr` was checked explicitly: hyD identifies the
image point with x, and its inverse transports a germ at x to the source stalk of
the composite map. The equation then lands in A/(hbar) on both sides. Naming i
introduces no extra choice because its equality fixes it to the quotient inclusion.
The point equality is equivalent to the stated fibre-point mapping by injectivity
of the original fibre projection. No mismatch was found and no mathematical
statement was changed. A docstring phrase was clarified to say that the maximal
ideal times the module A is proper.
