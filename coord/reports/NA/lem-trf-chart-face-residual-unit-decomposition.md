## Worker report

The module `Sheaf.TraceFormula.ChartFaceResidualUnitDecomposition` states
`Algebra.chart_face_residual_unit_decomposition`, with `sorry` as its only postponed
proof. It retains the accepted stage-1 statement and all eleven proof steps. The
canonical helper definitions are recorded in `lean.declarations`; their data is
fully constructed from existing Mathlib and project objects. No new independent
notion, new DAG node, dependency replacement, or statement correction is required.

The inherited BLOCKED ending concerned reopening a reviewed stage-1 split. This
assignment is stage 2: `coord/brief-stage2.md` §0 explicitly authorizes its Lean
statement. The current queue lists the item at stage 2 and the current node has
no Lean record. There is no released repair note for the item. The draft preserved
in the sandbox has been read against the current accepted node, its sources, and
its dependency declarations, then compiled on the live server.

### Hypotheses and objects

The Lean spelling is multiplicative throughout: `1` denotes additive zero,
products denote sums, inverses denote negatives, and `K × T` is the node's
Cartesian direct sum. This changes no monoid or hypothesis.

* `(A : Type u) [CommRing A] [IsLocalRing A]` is the nonzero commutative local
  ring: Mathlib's `IsLocalRing` extends `Nontrivial`. Its maximal ideal is
  `IsLocalRing.maximalIdeal A`. No Noetherian, domain, field or characteristic
  assumption has been added.
* `R : Type v`, `Q : Type w`, their `CommMonoid` instances, `hR` and `hQ` use
  `AlgebraicGeometry.IsFineSaturatedMonoid`. The published predicate specifies
  finite generation, injectivity of the canonical group-completion map, and
  saturation. Distinct arbitrary universes `u v w` are explicitly declared.
* `h : R →* Q` and `hh : Function.Bijective (groupMap h)` say precisely that the
  chart homomorphism induces a group isomorphism. `groupMap` is
  `GrothendieckGroup.lift (GrothendieckGroup.of.comp h)`.
* `α : R →* A` is the chart. `sourceFace α` abbreviates its inverse image of ring
  units. The existing `localizedUnitChart α` constructs the specified extension
  `α_G` on `Localization (sourceFace α)`, and `unitChartGroupMap α` is its
  canonical map to the original group completion. For an integral monoid,
  this localization is exactly the fraction submonoid `R_G` of the node.
* `sourceSharp α` abbreviates the multiplicative form of the published
  `chartSharpMonoid α`, hence `Associates (Localization (sourceFace α))`.
  `Associates` is quotient by multiplication by units, namely by `G^gp` here.
  `a : sourceSharp α →* A` is the specified monoid homomorphism, and
  `ε : GrothendieckGroup R →* Aˣ` is the specified group character. `hα`
  quantifies over every element of the localization and states
  `localizedUnitChart α x = ↑(ε (unitChartGroupMap α x)) * a (Associates.mk x)`.
  Thus the factorization is on all of `R_G`, not merely the original generators.
* `monoidChartTensor α h` is the existing ring
  `A ⊗[MonoidAlgebra ℤ R] MonoidAlgebra ℤ Q`, with actions induced by `α` and
  `h`. Its base map and monomials are the existing `monoidChartTensorBase` and
  `monoidChartTensorMonomial`. Monoid algebras are Mathlib's finitely supported
  sums with precisely the node's multiplication, not a formal placeholder.
* `q : Ideal (monoidChartTensor α h)` with `[q.IsPrime]` is the chosen prime;
  `hq` is its contraction to the maximal ideal of `A`. `Localization.AtPrime q`
  is exactly `B`. `targetFace α h q` is the inverse image of units under the
  existing `localizedTensorMonomial α h q`, so it is exactly `F`.
* `faceLocalization Q F` is the existing submonoid of the group completion
  consisting of `of q * (of f)⁻¹`. `faceGroup F` is the subgroup closure of the
  image of `F`. `chartRelations α h` is the image of `faceGroup G` under
  `groupMap h`, hence `N`. `GrothendieckGroup Q ⧸ chartRelations α h` is `M`.
* `residualMonoid F N` is the image of the actual `faceLocalization Q F` under
  `QuotientGroup.mk' N`, thus `P = Q_F/N` embedded in `M`, including all residual
  units. `residualUnits F N` is the image of `faceGroup F` in `M`, thus `K` as a
  subgroup. `targetSharp α h q` is `Associates (Localization F)`, the same
  sharpening construction giving `T`.
* `denominators α h F` is the image of `F` in `C`, exactly the multiplicative
  set of its face monomials. `Localization (denominators α h F)` is `C_F`, with
  the ring structure appropriate to the ring localization in the node.
  `tensorFraction` is Mathlib's actual ring-localization fraction. `fractionClass`
  is the specified class of `q/f` in the quotient monoid `P`.

### Clauses of the conclusion

1. The first two quantified conjunctions give the face condition for `G` and `F`;
   their submonoid structure is part of `sourceFace` and `targetFace`.
   `(targetFace α h q).comap h = sourceFace α` is exactly `h⁻¹(F)=G`.
2. The next two equivalences identify the units of `Localization G` and
   `Localization F` with membership in `faceGroup G` and `faceGroup F`, using
   the canonical maps `localizationGroup`. Under the integral fraction model
   these are precisely `R_Gˣ=G^gp` and `Q_Fˣ=F^gp`.
3. The two `IsFineSaturatedMonoid` conjuncts, the two implications
   `IsUnit s → s = 1`, and the two existentials
   `∃ n, Nonempty (Module.Basis (Fin n) ℤ (Additive (GrothendieckGroup ...)))`
   express that `S,T` are sharp fs with finite free group completions. Rank zero
   is permitted.
4. `chartRelations α h ≤ faceGroup F` makes the containment `N ≤ F^gp` explicit.
   The equivalence `eM : S^gp ≃* M` is fixed on every original `r` by its
   representative equation, so it is the induced group isomorphism. `π : M →*
   T^gp` is fixed on all original `Q`-generators by the following equation and
   is therefore the canonical quotient map, not an unconstrained map.
5. `eK` identifies `faceGroup F ⧸ N.comap (faceGroup F).subtype` with the actual
   subgroup `K` of `M`; its equation on every face-group representative fixes
   this identification. The comap is just `N` regarded as a subgroup of
   `F^gp`; the preceding containment verifies its meaning.
6. The quantified biconditional on `m : M` is exactly that `P` is the inverse
   image of the embedded `T` under `π`. The equation `π (σ t) = t` makes `σ`
   a group section and the next membership clause states `σ(T) ⊆ P`.
7. `eP : P ≃* (K × T)` and its inverse formula
   `↑(eP.symm (k,t)) = ↑k * σ (GrothendieckGroup.of t)` are the specified
   product decomposition. The finite-basis existential for `Additive K` is
   exactly finite freeness of `K`.
8. `f : S →* (K × T)` is fixed on every image of an original `r` by
   `f (sharpMap G r) = eP (fractionClass F N (h r) 1)`. Since the sharp
   localization is generated by these images (the inverted elements become
   units and hence become `1` in the sharp quotient), this is exactly the
   induced chart map. The implication `s ≠ 1 → (f s).2 ≠ 1` is the required
   condition on its `β` coordinate. The next biconditional is precisely the
   final criterion `q ∉ F` iff its `T`-coordinate is nonzero.
9. `Φ : Localization (denominators α h F) ≃+* monoidChartTensor a f` is the
   asserted isomorphism. The target is the actual balanced tensor ring
   `A ⊗[ℤ[S]] ℤ[K × T]` with exactly the `a` and `f` actions. The equation on
   every `b : A` states preservation of the actual coefficient maps, giving
   exactly the claimed `A`-algebra isomorphism without an arbitrary additional
   algebra instance on the bundled chart ring.
10. `character h hh ε` is `ε` composed with the inverse multiplicative equivalence
    obtained from `groupMap h` and its bijectivity proof. The next equation on
    every `z : Q` is `Φ([z])=χ(z)[class(z)]`, with `eP` supplying its `(k,v)`
    coordinates. The equation on `tensorFraction ... z d` is precisely
    `Φ([z]/[d])=χ(z-d)[class(z-d)]`. A monomial indexed by `(k,v)` is the product
    of the `k` and `v` basis monomials by Mathlib's monoid-algebra multiplication.
11. The prime `qD` is specified by contraction under `C → C_F → D`, retaining
    the selected prime. Since all face denominators are inverted, this
    specifies its transport from `q`. `eB` identifies the actual prime
    localizations and its equation on every `c : C` makes this the induced
    localization map. `eHat` identifies their maximal-ideal completions and
    preserves the maps from `B`. Finally `eN` identifies their quotients by
    every maximal-ideal power, preserving representatives and intertwining
    `AdicCompletion.evalₐ` with `eHat`. This spells out the compatible-sequence
    meaning of the induced completion isomorphism in node proof step 11.
12. No injectivity of the sharp map `S^gp → T^gp` is assumed or concluded.

### Dependencies and source inspection

The node's recorded dependency declarations were read at their actual source:

* `def-trf-fs-log-blowup`: `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`,
  `AlgebraicGeometry.IsSaturatedLogBlowup` and its public imports. The relevant
  monoid predicate is `AlgebraicGeometry.IsFineSaturatedMonoid` in
  `Sheaf.AlgebraicGeometry.LogRegularPair`, read with its entire definition.
* `def-weil-pbc-module-tensor-product`: `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`; its quotient construction is used
  by the published `monoidChartTensor`.
* `def-weil-pbc-localization-at-prime`: `Localization.AtPrime` in
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, read with its docstring.
* `def-weil-pbc-adic-completion`: `AdicCompletion` in
  `Mathlib.RingTheory.AdicCompletion.Basic`, and the ring structure and `evalₐ`
  in `Mathlib.RingTheory.AdicCompletion.Algebra`. These are the actual inverse
  limits and finite-level evaluations.
* `def-weil-pbc-module-localization`: its module specialization is
  `LocalizedModule` in `Mathlib.Algebra.Module.LocalizedModule.Basic`. The
  present ring specialization uses Mathlib's `Localization` ring and its
  fraction operations; the underlying localization is the same universal
  localization, with multiplication also retained. No alternative localization
  definition is introduced.

The existing canonical chart constructions are imported from
`Sheaf.RingTheory.FormalMonoidExtensionModel`: `Algebra.monoidChartTensor`,
`monoidChartTensorBase`, `monoidChartTensorMonomial`, `chartSharpMonoid`,
`localizedUnitChart`, `unitChartGroupMap` and `localizedTensorMonomial`. Their
full signatures and constructions were read, and they are reused rather than
copied. Only these data constructions are used; the downstream theorem
`formalMonoidExtension_model` is not used to prove this lemma. A future proof of
that downstream theorem will need its existing chart helpers factored into a
common import to avoid an import cycle; this delivery does not add a DAG edge
to the downstream theorem or use it as a hypothesis.

The proof plan is transcribed step by step in the main theorem docstring.
`AlgebraicGeometry.face_sharpening` and the canonical `Algebra.faceLocalization`
and `Algebra.faceLocalizationGroupMap` were read in
`Sheaf.TraceFormula.FsFaceSharpening` and `Sheaf.TraceFormula.FaceLocalizationFs`.
These modules are imported. The other stated proof dependencies are Mathlib
`Submodule.basisOfPid` (finite free subgroup), the monoid-algebra lift APIs,
`Algebra.TensorProduct.productMap` and `ext`, and
`IsLocalRing.notMem_maximalIdeal`; their recorded source signatures and
adjacent docstrings were read. Their modules are imported for stage 3.
`lem-trf-group-section-monoid-product` has no recorded Lean declaration, so no
invented import is provided for it.

The ILO PDF was opened through `pdftotext`, PDF pp. 76--77 and 104--106, giving
printed p. 70 and pp. 98--99: VI 1.6 describes the two formal chart models;
VIII 3.1.1 defines sharpening, 3.1.2 identifies integral monoid localization
with the fraction submonoid, and 3.1.5 defines local monoid maps. As the node
explicitly says, the tensor/character formula is its agent-supplied algebraic
refinement, not a verbatim ILO theorem. The current blueprint unit
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/_section.md`
was also read; its newer contracting-correspondence route does not alter this
accepted algebraic subnode, and no unit statement is changed.

### Edge cases and searches

Checked the trivial source and target monoids, rank-zero bases, all units
(`G=R`, `F=Q`, `S=T=1`), trivial residual group `K`, and trivial `T` with
nontrivial residual units. The direct product and basis types include all these
cases. The zero ring is excluded exactly as in the node, by `IsLocalRing`.
Torsion in `R^gp,Q^gp` is allowed; it is only the sharp group completions and
`K` that are concluded free. No injectivity of `β^gp` is inadvertently imposed.
The identity chart and nontrivial unit character preserve both displayed
monomial formulas: the twist is `χ`, not its inverse, on the forward map.
Nonreduced local rings and arbitrary characteristic are not excluded. At
completion level `n=0`, both quotients are the zero ring and the equations
remain well typed.

Searches performed with the prescribed `msearch.py` wrapper:

* LeanFinder: “fine saturated monoid face localization residual units character
  twisted tensor algebra decomposition”: 8 hits, including
  `IsLocalization.tmul_mk'`, `IsLocalization.mk'_tmul` and algebra-presentation
  base-change results; none states the residual splitting or character formula.
* Loogle: `MonoidAlgebra, Localization`: no hits.
* Mathlib grep: `faceLocalization|residualMonoid|ChartResidual|residual_unit_decomposition`:
  no hits.
* LeanSearch: “splitting face localized monoid into residual unit group and sharp
  quotient with character twisted monoid algebra isomorphism”: 8 hits, including
  `IsLocalization.atUnits`, `Localization.algEquiv`, `MulChar.ofUnitHom`, and
  `IsLocalization.submonoid_map_le_is_unit`; these supply portions of the
  localization/character API, not the lemma.
* Project/source `rg`: the exact names `ChartResidual`,
  `chart_face_residual_unit_decomposition`, `residualMonoid`, and `residualUnits`
  do not occur in either `lean/WeilConjectures` or `lean/Sheaf`. The required
  grep for this blueprint id in `lean/WeilConjectures` found no match.
  Broader searches for `faceLocalization`, `chartSharpMonoid`,
  `monoidChartTensor`, face subgroups and group-completion maps located the
  existing helpers listed above. `LogChartFaceTor.face` and its sharp map were
  read too: they use a common universe and the fraction-submonoid realization,
  while here source/target faces are transparent abbreviations of unit preimages
  and the sharp maps use the already published `Localization` realization.
  No independent duplicate chart or tensor ring was introduced.

No unresolved statement dispute was found. The old stage-1 concern that `a` and
`ε` must be homomorphisms was already resolved in the accepted node; the Lean
binders explicitly require both, as does the current statement.

Validation: the module compiled separately through `scompile.py` against the
live server library, both sandbox and library-module checks clean (8.4 s and
7.4 s). All variables and universes are explicit, `autoImplicit` is false,
all lines are at most 100 characters, and the only postponed theorem is the
item's statement. Delivery preflight and its compile are run by `deliver2.py`.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
