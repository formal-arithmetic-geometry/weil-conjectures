## Worker report

This repairs returned immutable head `9cbf7856d902` in the retained packet. The module
`Sheaf.TraceFormula.CompletedJacobianDifferentials` states
`AlgebraicGeometry.completedJacobianDifferentials`. Its only theorem, with the matching
DAG node, has proof `sorry`. All abbreviations, maps, the predicate, and the tensor module
structure have real data. No natural-language statement, dependency list, or proof is changed.
The saved node's non-`lean` fields were compared with the current shared node and agree;
the prescribed delivery wrapper rebases the packet on the current `newtargets-dag`.

The four returned H3 points are repaired as follows.

1. **Tensor order.** `completedDifferentialTarget k S p` is literally
   `TensorProduct (completedLocalRing S p)
     (KaehlerDifferential k (completedLocalRing S p)) (completedRing S p)`:
   `Ω[A/k] ⊗[A] Â`, not the reversed tensor. The completion acts on the right tensor
   factor by transport through Mathlib's `TensorProduct.comm`. The named `SMul` and
   `Module` instances construct that action, and compatibility with the universal
   derivation is the exact element `da ⊗ 1` in this order.
2. **Relations in the variable ideal.** `hf` says, for every `j : Fin s`,
   `f j ∈ Ideal.span (Set.range (fun i : Fin n ↦ MvPowerSeries.X i))`.
3. **Canonical continuous extension.** There is no derivation parameter or assumed
   existence of an extension. The conclusion supplies `dhat`, its defining properties,
   and uniqueness among all derivations with those properties. The helper
   `IsCompletedDifferentialExtension p σ dhat` means adic continuity, the identity
   `dhat (AdicCompletion.of _ _ a) = da ⊗ 1` for every `a : A`, and
   `dhat (σ c) = 0` for every `c : F`. Existence and uniqueness render the node's
   reference to *the* continuous extension, which its first proof step explicitly
   obtains from `lem-trf-completion-kahler-differential-comparison` (i).
4. **Residue map.** The unconstrained parameter `ρ` is removed.
   `completedResidueMap p` evaluates a compatible sequence with `AdicCompletion.evalOneₐ`
   to `A/pA`, transports the ideal by
   `IsLocalization.AtPrime.map_eq_maximalIdeal`, and applies the inverse of
   `IsLocalization.AtPrime.equivQuotMaximalIdeal p A`. Thus `hsection` is a section
   of the canonical reduction to `S/p`, with no arbitrary residue-field automorphism.

The formerly delivered auxiliary theorem `completedJacobian_range_le_kernel` was also
false without relation hypotheses (take `π = id`, `f = t`, and a nonzero coordinate
derivation). It is removed, rather than kept as an unrelated `sorry`. Well-definedness
and invertibility are now expressed together by a linear equivalence out of the actual
Jacobian cokernel, with its composite with the quotient map specified. No additional
postponed theorem is introduced.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The field is `(k : Type u) [Field k]`. The commutative algebra is
  `(S : Type v) [CommRing S] [Algebra k S]`. The universes are independent.
  `hfinite : RingHom.FiniteType (algebraMap k S)` is finite generation over `k`.
- `(p : Ideal S) [p.IsMaximal]` is the specified maximal ideal. Its primality is
  inferred from maximality, so no separate prime-ideal hypothesis is imposed.
- `completedLocalRing S p` is Mathlib `Localization.AtPrime p`. `completedIdeal S p`
  is the mapped ideal `pA`, and `completedRing S p` is `AdicCompletion (pA) A`.
  `F` is the exact quotient `S ⧸ p`, with its induced `k`-algebra structure.
- `[FiniteDimensional k (S ⧸ p)]` and `[Algebra.IsSeparable k (S ⧸ p)]` express the
  finite separable residue-field extension.
- `σ : (S ⧸ p) →ₐ[k] completedRing S p` and `hsection` express the fixed coefficient
  section of the canonical residue map. The `F`-action in the node is through `σ`.
- `(n s : ℕ)` permits any finite variable and relation families, including empty ones.
  `f : Fin s → MvPowerSeries (Fin n) (S ⧸ p)` and `hf` express the given generators
  and their membership in the ideal of variables.
- `π` is the given ring homomorphism from that exact power-series ring;
  `hπcoeff : ∀ c, π (MvPowerSeries.C c) = σ c` makes it an `F`-algebra homomorphism
  for the specified action. This is the unbundled version of the node's algebra map,
  with no additional arbitrary `Algebra F Â` instance.
- `hπsurj` is surjectivity. `hπcontinuous` is explicit `Continuous`: the source uses
  `MvPowerSeries.WithPiTopology.instTopologicalSpace` with discrete coefficients
  (`⊤`), which for finitely many variables over a field is the variable-adic topology;
  the target uses the adic topology of the extended ideal `pA Â`.
- `hkernel : RingHom.ker π = Ideal.span (Set.range f)` gives exactly the kernel.
- The first conclusion supplies the unique continuous extension, as detailed above.
  Its continuity predicate is `∀ r, ∃ N, dhat ((pA Â)^N) ⊆ (pA Â)^r M`, the
  neighborhood-of-zero criterion for an additive map between these adic topologies.
- `completedJacobianMatrix` is the `Fin n` by `Fin s` matrix
  `fun i j ↦ π (MvPowerSeries.pderiv (S ⧸ p) i (f j))`. Its `Matrix.toLin'` map
  goes from `(Fin s → Â)` to `(Fin n → Â)`, so the quotient by its `LinearMap.range`
  is precisely the stated cokernel, with the correct column convention.
- The conclusion supplies `e : (Â^n / range J) ≃ₗ[Â] M` and requires
  `e (mkQ v) = completedDifferentialCoordinateMap p n π dhat v` for every `v`.
  The latter map is the actual finite linear combination of
  `dhat (π (MvPowerSeries.X i))`. On each standard basis vector it is exactly the
  node's prescribed differential. Conversely the basis images determine the map,
  so this is the claimed canonical map, including its well-definedness and bijectivity.

Dependency declarations read and used:

- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType` and `Algebra.FiniteType`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`,
  `IsLocalization.AtPrime.map_eq_maximalIdeal`, and `equivQuotMaximalIdeal`.
- `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable` (Stacks 09H1).
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`,
  `AdicCompletion.of`, and `AdicCompletion.evalOneₐ`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`, `.Derivative`, and `.PiTopology`:
  `MvPowerSeries`, `C`, `X`, `pderiv`, and the explicit product topology.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `KaehlerDifferential.D`,
  and its universal-property interface `linearMapEquivDerivation`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs` and `.Basic`: `TensorProduct`, `tmul`,
  and `comm`. The tensor dependency is a Mathlib leaf without a `lean` record.
- The proof-only Mathlib dependency `Algebra.FormallyUnramified.of_isSeparable`
  is imported through `Mathlib.RingTheory.Unramified.Field`. The other two proof-only
  continuous-differential comparison nodes have no recorded Lean module in the current
  shared DAG, so their mathematical proof plan is given in the theorem docstring.

Source verification: read Stacks `curves.tex`, Tag 0C4D, the polynomial Jacobian
presentation and completion passage, and `varieties.tex`, Tag 0C52, the residue-preserving
coefficient-field section. As the node's source record already explains, this item is the
auxiliary completed comparison extending that argument, not a verbatim standalone lemma
of Tag 0C4D. The theorem docstring gives all four proof steps and identifies the precise
comparison and power-series presentation dependencies.

Searches for existing declarations (in addition to the searches retained with the node):

- `msearch.py` LeanFinder: "Jacobian cokernel of a complete local algebra with finite
  separable residue field and the canonical continuous extension of Kahler derivation".
  Eight hits, including `Algebra.Extension.toKaehler`,
  `Algebra.Presentation.differentials.comm₂₃`, and ordinary cotangent presentations;
  no completed-local comparison or canonical continuous-extension theorem.
- `msearch.py` Loogle: `KaehlerDifferential, AdicCompletion`: zero hits.
- `msearch.py` grep: `completion.*differential|differential.*completion` in `RingTheory`:
  zero hits.
- `rg` over `WeilConjectures/` and shared `lean/Sheaf/` for the item id,
  `completedJacobianDifferentials`, `IsCompletedDifferentialExtension`, and
  `completedResidueMap`: no existing theorem or extension/residue helper.
  The landed `Algebra.HasCompletedJacobianPresentation` is a predicate asserting a
  related presentation, not a theorem proving this node with the given canonical
  residue section and unique continuous extension. Its source and node were read;
  it is not an exact existing match.
- Source searches for completion evaluation and localization residue equivalences
  found the Mathlib constructions used in `completedResidueMap`; no map is replaced
  by an arbitrary choice.

Edge cases checked mathematically: `n = 0` gives a coefficient field and zero differentials,
with every `f j = 0`; `s = 0` gives the free continuous differential module; the presentation
`F[[t]]/(t)` has Jacobian `[1]` and zero target; redundant zero equations add zero columns;
`F[[x,y]]/(xy)` has column `(y,x)` and the expected relation `y dx + x dy = 0`.
These tests work in characteristic two as well. The identity residue extension and section
are included. The zero ring has no maximal ideal and is correctly excluded by the actual
hypotheses. The theorem does not assume an algebraically closed field, positive dimension,
minimal variables, or nonempty relation families. No `STATEMENT-DISPUTED` flag is needed.

## Second reading by ND

I reread the retained node and the repaired file in a separate checking pass, with all four
returned H3 defects open. The written tensor order and element `da ⊗ 1` now agree; `hf`
contains the previously missing variable-ideal condition; there is no free `ρ` and the
section composite uses evaluation modulo `pA` and the canonical localization equivalence;
and the derivation is constructed by the theorem's existence conclusion with explicit
uniqueness, not assumed in its binders. The coefficient compatibility, source and target
topologies, exact kernel, and both finite index types are present. The isomorphism's
quotient composite fixes every basis image and therefore specifies the whole map.
The false unconstrained auxiliary range lemma has been deleted. All helpers are real
constructions of this node's own rings/maps or its explicit extension predicate; only the
main, matching theorem is postponed. This pass found and removed the redundant prime
binder, separated the field and algebra universes, and expanded the proof docstring.
No node statement correction, new node, or dependency module is required.
