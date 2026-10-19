## Worker report

Repair of the returned stage-2 head e303240e36de, points H1 and H2.

H1 is repaired by the new module `Sheaf.AlgebraicGeometry.RelativeCurveFactorization`,
with the single theorem `AlgebraicGeometry.exists_relativeCurveFactorization` and its
whole proof `by sorry`. The module and theorem docstrings cite ILO, Travaux de Gabber,
Expose X, proof of Theorem 3.5, Step 5, printed p. 163. The theorem docstring includes
all nine proof steps of the current DAG node, including their dependency citations.
The source PDF was opened at PDF pages 168--169: Step 5 constructs a rational map
and replaces its domain by its schematic graph image, an isomorphism over the open
where that map is defined. The blueprint unit `sk-i-curve-zero/_section.md` was also
read; its own statement is not changed.

H2 is repaired by taking the node afresh from current `newtargets-dag` and changing
only its `lean` field. In particular `split_report.summary` is exactly the current
base value; no stage-1 report sentence is re-sent. The retained sandbox contained
no module or node file at the start of this repair. No git command or direct edit
was made in the shared checkout, and all delivery files are in the assigned sandbox.

The statement is unchanged. No new node, dependency repair, new definition, statement
correction or mathematical dispute is needed.

Clause-by-clause rendering:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| Schemes X and S, arbitrary size | `{S X : Scheme.{u}}`, with `universe u` explicitly declared and `autoImplicit false`. All output schemes and presenting rings are in the same arbitrary scheme universe, with no restriction to small schemes or a fixed universe. |
| S is the spectrum of a field | The first alternative of `hS` is `∃ (k : Type u) (_ : Field k), Nonempty (S ≅ Spec (.of k))`. An arbitrary base is retained up to scheme isomorphism. |
| Or S is an excellent integral trait | The second alternative of `hS` is `∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R), IsExcellent R ∧ Nonempty (S ≅ Spec (.of R))`. The DVR class includes locality, principality and exclusion of fields. |
| s is the generic point of S | `(s : S) (hs : IsGenericPoint s Set.univ)`. This uses the recorded generic-point predicate, without an extra integral-base hypothesis. |
| X to S | `(f : X ⟶ S)`, the specified morphism. |
| f proper | `[IsProper f]`, Mathlib's exact notion. |
| f dominant | `[IsDominant f]`, Mathlib's dense-range class, explicitly requested in the return. |
| f finite type | `(hft : LocallyOfFiniteType f ∧ QuasiCompact f)`, exactly the pair recorded on `def-weil-finite-type-morphism`. It remains explicit even though properness implies it. |
| X integral | `[IsIntegral X]`, including nonemptiness. |
| d at least one | `(d : ℕ) (hd : 1 ≤ d)`. |
| Generic fibre dimension d | `hdim : topologicalKrullDim (f.fiber s) = (d : WithBot ℕ∞)`. This is the scheme-theoretic fibre of the recorded declaration. |
| Existence of Y over S | `∃ (Y : Scheme.{u}) (q : Y ⟶ S) ...`. |
| Y excellent | `∀ U : Y.Opens, IsAffineOpen U → IsExcellent Γ(Y, U)`, exactly all affine coordinate rings. |
| Y integral | `IsIntegral Y`. |
| Y projective over S | `IsHProjective q`, the recorded finite projective-space embedding convention. |
| Y dominant and finite type over S | `IsDominant q ∧ LocallyOfFiniteType q ∧ QuasiCompact q`. |
| Generic fibre of Y has dimension d minus one | `topologicalKrullDim (q.fiber s) = ((d - 1 : ℕ) : WithBot ℕ∞)`. The same point s is used; natural subtraction is correct because `hd` excludes d = 0. |
| Excellent integral X0 | The existential scheme `X₀`, followed by `∀ U : X₀.Opens, IsAffineOpen U → IsExcellent Γ(X₀, U)` and `IsIntegral X₀`. |
| Proper dominant a from X0 to X | `(a : X₀ ⟶ X)` followed by `IsProper a ∧ IsDominant a`. |
| a finite over a dense open of X | `∃ U : X.Opens, Dense (U : Set X) ∧ IsFinite (a ∣_ U)`. The restriction is precisely from a-inverse-image U to U, not a restriction to an unrelated domain open. |
| Proper dominant g from X0 to Y | `(g : X₀ ⟶ Y)` followed by `IsProper g ∧ IsDominant g`. |
| Equal composites over S | `a ≫ f = g ≫ q`. |
| Generic function fields mean generic residue fields | `∃ η : X₀, IsGenericPoint η Set.univ ∧ ...`, using the generic point as an existential witness rather than introducing a second definition of function field. Since g is dominant and X0 is integral, g sends η to the generic point of Y: continuity sends every specialization of η to a specialization of g η, and density then forces the closure of g η to be all Y. |
| The extension induced by g has transcendence degree one | `@Algebra.trdeg (Y.residueField (g η)) (X₀.residueField η) _ _ (g.residueFieldMap η).hom.toAlgebra = 1`. This specifies the canonical residue-field homomorphism of g, with no arbitrary field map or algebra structure. A unital map of fields is injective, so this is the stated inclusion. |

Recorded statement dependencies used (all signatures and docstrings were read):

- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper :: AlgebraicGeometry.IsProper, AlgebraicGeometry.IsSeparated, AlgebraicGeometry.UniversallyClosed`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType :: AlgebraicGeometry.LocallyOfFiniteType, AlgebraicGeometry.QuasiCompact`.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties :: AlgebraicGeometry.IsIntegral`.
- `def-exc-excellent-ring`: `Sheaf.RingTheory.ExcellentRing :: IsPrimeChain, IsSaturatedPrimeChain, IsCatenaryRing, IsUniversallyCatenary, IsQuasiExcellent, IsExcellent`.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber :: AlgebraicGeometry.Scheme.Hom.fiber, AlgebraicGeometry.Scheme.Hom.fiberι, AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField`.
- `def-kun-dimension`: `WeilConjectures.Mathlib.Topology.KrullDimension :: topologicalKrullDimAt, topologicalKrullDim`.
- `def-kun-projective`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective :: AlgebraicGeometry.IsHProjective`.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite :: AlgebraicGeometry.IsFinite, AlgebraicGeometry.IsIntegralHom`.
- `def-sc-generic-point`: `Mathlib/Topology/Sober.lean :: IsGenericPoint`.
- `def-kun-transcendence-degree`: `Mathlib.RingTheory.AlgebraicIndependent.Basic :: Algebra.trdeg`.
- `def-sc-discrete-valuation-ring`: `Mathlib/RingTheory/DiscreteValuationRing/Basic.lean :: IsDiscreteValuationRing`.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField :: AlgebraicGeometry.Scheme.residueField, AlgebraicGeometry.Scheme.Hom.residueFieldMap`.

`IsExcellent` is the existing full ring predicate in
`Sheaf.RingTheory.ExcellentRing`. `IsHProjective` was read both from the canonical
shared upstream source and through `scompile.py --source` on the current server.
The projective convention agrees with `def-kun-projective`. The generic-point,
DVR, dimension, fibre and residue-field interfaces require no specialization repair.

Every recorded proof dependency with a published module is imported, using ordinary
(non-public) imports for proof-only modules; Mathlib proof leaves are imported from
the files in their matches. The recorded base-change module was read through
`scompile.py --source WeilConjectures.AlgebraicGeometry.BaseChangeConventions`.
There are no omitted proof-dependency imports or import cycles.

Edge cases checked before writing:

- d = 1 gives d - 1 = 0. The construction can take Y = S, X0 = X, a the identity
  and g = f; the transcendence-degree assertion is precisely the dimension-one
  generic-fibre assertion. No positive-dimensional Y hypothesis is added.
- d = 0 is excluded exactly by the node's hypothesis `hd`, rather than accidentally
  by a projective-coordinate index type.
- The empty scheme X is excluded by `IsIntegral X`. A dense open U of integral X
  is nonempty, so generic finiteness cannot be witnessed by an empty open.
- Empty affine opens are included in the excellence quantifiers, as the node asks
  for every affine coordinate ring; their zero coordinate ring causes no added
  nonemptiness condition.
- Finite and imperfect base fields, arbitrary characteristic and inseparable
  generic field extensions are permitted. No perfectness, separability, smoothness,
  algebraic closedness, infinitude or flatness hypothesis was introduced.
- The DVR alternative explicitly includes `IsDomain R`; the DVR class excludes
  fields and the excellence predicate is only assumed in that alternative.
- Non-affine Y and X0 are allowed; excellence does not mean just excellence of
  their global sections. Neither a nor g is assumed to be an isomorphism, finite
  everywhere, or smooth. Only the dense-open restriction of a must be finite.
- The last field map is exactly `g.residueFieldMap η`; it cannot vary independently
  of g. Its source is the generic residue field of Y by dominance.

Searches for an existing exact declaration:

- `msearch.py leanfinder`, query "proper dominant integral scheme over field or
  excellent discrete valuation ring factorization relative curve transcendence
  degree one": eight hits, including `finite_appTop_of_universallyClosed`,
  `isField_of_universallyClosed`, `IsIntegral`, `IsIntegralHom`,
  `Scheme.PartialMap.fromFunctionField` and normalization dominance. None states
  this factorization.
- `msearch.py loogle`, query `AlgebraicGeometry.IsDominant,
  AlgebraicGeometry.Scheme.Hom.residueFieldMap`: zero hits for the combined query.
  Each constituent API was read in its defining Mathlib module.
- `msearch.py grep`, query `relativeCurve|curve_factorization|functionFieldMap`,
  subdirectory `AlgebraicGeometry`: zero hits.
- `msearch.py leansearch`, query "A proper dominant integral scheme over a field
  or excellent discrete valuation ring admits a generically finite modification
  factoring through a projective scheme with relative function field transcendence
  degree one": eight hits on properness, integral morphisms and dominance,
  with no exact factorization theorem.
- `rg -n` for `relativeCurve|curve_factorization|relative.curve.factor|functionFieldMap|
  genericallyFinite` in the upstream project and side `lean/Sheaf`: no existing
  exact factorization. `grep -rn` of the node id in upstream Lean: no hits.
- `rg -n exists_relativeCurveFactorization` in the upstream declaration index,
  Mathlib, upstream project and side `lean/Sheaf`: no existing declaration.
- `rg -n` for excellent-scheme predicates and affine-coordinate excellence in
  side `lean/Sheaf` and `lean/WeilConjectures`: no distinct reusable scheme
  predicate; the statement directly applies the recorded ring predicate.

Compile evidence: the first server `scompile.py Q32
lem-trf-relative-curve-factorization <RelativeCurveFactorization.lean>` run accepted
both the sandbox and library forms (5.7 s and 14.0 s), but reported the redundant
instance-binder overlap between `IsProper f` and `LocallyOfFiniteType f`. This was
repaired by giving the finite-type pair as the explicit proposition `hft` above,
retaining both hypotheses without overlapping instance binders. The revised server compile returned exit code 0 with no errors or warnings in
either form. The library-form compile reported 3.9 s; the sandbox-form elapsed
time included the server slot queue. Every Lean invocation retained the default
60 s limit after slot acquisition. Final dry-run evidence is recorded below.

## Second reading by Q32

The direct-worker delivery rule supplies the maintainer's independent review;
no second worker was started. This section records a separate second pass by Q32,
not an independent-agent review.

I reopened the current node and the final module and checked the rows above against
the actual signature. In particular I checked that both base alternatives remain,
that properness, dominance, the explicit finite-type pair, integrality, the generic
point and the exact dimension d are present, and that all output conjunctions are
under one choice of Y, q, X0, a and g. Y has excellence on all affine opens,
integrality, H-projectivity, dominance, finite type and dimension d - 1 at the same
s. X0 has the same affine-ring excellence condition and integrality. The map a
has properness, dominance and finiteness over a dense target open; g has properness
and dominance; the composites are equated in Lean's composition order.
The generic-residue-field witness uses the specified map g and the canonical
residue-field map. Its trdeg is one, with no independent algebra witness.
All 12 dependency definitions are reused, and the nine source proof steps remain
in the theorem docstring.

The only mismatch found during validation was the linter overlap from redundant
instance binders; the finite-type condition was retained as `hft` to remove that
warning. No mathematical clause, node statement, dependency list, proof, source,
or stage-1 split report was changed. The node's sole modified field is `lean`.

Final dry-run evidence: `deliver2.py Q32 lem-trf-relative-curve-factorization --no-push`
returned exit code 0 and printed `OK (dry run): commit bc119b6331 passes the preflight
and compiles; nothing pushed`. Its exact staged packet was the theorem module, the
item node and this report. No dependency modules or new nodes were staged.
