## Worker report

The module `Sheaf.AlgebraicGeometry.IntegralChowEnvelopeCompactification` states
`AlgebraicGeometry.exists_integral_chow_envelope_compactification`, with its sole proof
`sorry`. The node is unchanged except for `lean`. There are no new definitions, dependency
repairs, or statement corrections. The docstring gives all nine steps of the recorded proof.

Hypothesis and conclusion correspondence:

- The schemes are `S R : Scheme.{u}` with arbitrary explicit universe `u`.
  Affine Noetherian base is `[IsAffine S] [IsLocallyNoetherian S]`, precisely the node's
  affine and locally Noetherian convention (affineness implies quasi-compactness).
- The separated finite-type morphism is `f : R ⟶ S`, with `[IsSeparated f]`,
  `[LocallyOfFiniteType f]`, and `[QuasiCompact f]`. Integrality is `[IsIntegral R]`.
- The unique generic point `ξ` is represented by `genericPoint R`. Its function field `L`
  is `R.functionField`, the generic stalk; for an integral scheme this is a field and
  canonically its residue field. This uses exactly the arbitrary-integral-scheme clause
  of `def-sc-function-field`. No field extension or choice of a different field is assumed.
- `n : ℕ` expresses `n ≥ 0`; `ProjectiveSpace (ULift.{u} (Fin (n + 1))) S` is classical
  projective n-space. The lift puts the finite coordinate type in the scheme universe.
- `Y Z : Scheme.{u}` and the existential witnesses `IsIntegral Y`, `IsIntegral Z`,
  together with `IsNoetherian Y ∧ IsNoetherian Z`, express all four scheme properties.
- The witnesses `π`, `j`, `c`, and `e` have exactly the specified domains and codomains.
  `IsProper π ∧ Surjective π`, `IsImmersion j`, `IsClosedImmersion c`, and
  `IsOpenImmersion e ∧ Dense (Set.range e)` render their respective properties.
- `e ≫ c = j` is the factorization. `j ≫ (ProjectiveSpace ... S ↘ S) = π ≫ f`
  makes `j` a morphism over S. The structure map of Y is `π ≫ f` and that of Z is
  `c ≫ (ProjectiveSpace ... S ↘ S)`; the displayed equalities also make π, c, and e
  morphisms over S, without adding unspecified structure maps.
- `IsProper (c ≫ (ProjectiveSpace ... S ↘ S))` is properness of Z over S.
- `c.ker = Scheme.IdealSheafData.vanishingIdeal ⟨closure (Set.range j), isClosed_closure⟩`
  asserts exactly the reduced induced closed structure on the closure of j(Y), rather
  than merely its underlying set. By the recorded reduced-induced-closed-subscheme
  theorem, the canonical vanishing-ideal subscheme has that image and reduced structure;
  a closed immersion with this kernel is the same closed subscheme up to its unique
  ambient isomorphism. Thus both the image-closure and scheme-structure clauses are present.
- `U : R.Opens`, `(U : Set R).Nonempty`, `Dense (U : Set R)`, and `IsIso (π ∣_ U)`
  express the nonempty dense open and its inverse-image restriction isomorphism.
- `a : Y.functionField ≅ R.functionField` and `b : Z.functionField ≅ R.functionField`
  identify both fields with L. These are isomorphisms in CommRingCat, hence field
  isomorphisms. `Spec.map a.hom ≫ Y.fromSpecFunctionField ≫ π = R.fromSpecFunctionField`
  identifies the generic map to R. The final equality identifies the generic map
  transported along e with `Spec.map b.hom ≫ Z.fromSpecFunctionField`. Composing it
  with c and using `e ≫ c = j` yields exactly the required equality in projective
  space. It introduces no arbitrary generic map. The first equation forces a to be the
  field identification coming from the dense-open isomorphism: that open contains the
  generic point, and π has a unique lift there. The second similarly forces b to be
  the identification induced by e. The projective compatibility is the composite of
  this same equation, not an additional independent identification.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`,
  `LocallyOfFiniteType.isLocallyNoetherian` (the latter for the proof plan).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, `IsSeparated`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact` and
  `QuasiCompact.compactSpace_of_compactSpace` (available through the public imports).
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`.
- `Mathlib.Topology.Sober`: `IsGenericPoint`, `genericPoint`, `genericPoint_spec`.
- `WeilConjectures.AlgebraicGeometry.FunctionField`: the recorded node's component-product
  declaration and its documented integral specialization to Mathlib `Scheme.functionField`.
  The latter's full definition and field instance were read in
  `Mathlib.AlgebraicGeometry.FunctionField`. Only this integral specialization is needed.
- `WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField`: `Scheme.fromSpecFunctionField`,
  the existing canonical map `X.fromSpecStalk (genericPoint X)`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`: `IsImmersion` (the immersion clause
  already identified by `def-weil-closed-immersion.mathlib_match`).
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `ProjectiveSpace`, its canonical
  structure morphism, and `ProjectiveSpace.instIsProper` (proof dependency).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme`, including the explicit
  kernel equality, image equality, and unique ambient isomorphism clauses.
  Its existing `Scheme.IdealSheafData.vanishingIdeal` and `Scheme.Hom.ker` constructions
  are used directly, without copying them.
- Proof-only imports are `WeilConjectures.AlgebraicGeometry.ChowLemma`
  (`ChowModification.nonempty_data`) and
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper`
  (`IsProper.of_isClosedImmersion`, `IsProper.isClosedImmersion_comp`,
  `IsProper.isClosed_range`). All stated proof dependencies are provided by these
  or the public statement imports. No proof import has been omitted.

Sources inspected: Stacks `limits.tex`, label `lemma-Noetherian-dvr-valuative-proper`
(Tag 0208), its proof of (4) implies (1), and `coherent.tex`,
`lemma-chow-Noetherian` (Tag 0200). The first uses the birational Chow map and the
closure of an irreducible component in projective space; the node's accepted split
makes the reduced closure of the generic preimage explicit and records the generic
field compatibility. The reduced-structure dependency signature and its docstring were
read in full. The example CompactObject module has been withdrawn; its node now points
to the identical upstream `WeilConjectures.CategoryTheory.CompactObject`, which was read.

Edge cases checked before drafting: integral schemes exclude the empty R, Y, and Z;
S may be nonreduced or disconnected. Empty S admits no f from integral R. A field
spectrum R is permitted. The case n=0 has one homogeneous coordinate, not an empty
coordinate type. The source R need not be proper or affine. The auxiliary Chow source
may have extra components or nilpotents; taking the reduced closure of the inverse
image of U removes both problems without a hidden hypothesis. No normality,
characteristic condition, perfectness, or excellence is assumed. A nonempty open in
integral R is dense and contains its generic point; both are explicitly retained in
the conclusion as the node asks. All schemes, rings, and coordinate types use the same
arbitrary universe, with a lift only for the finite coordinate type.

Searches actually run:

- `msearch.py leansearch`, query “An integral scheme of finite type separated over an
  affine Noetherian scheme admits an integral Chow modification and a reduced projective
  closure”: eight hits on `isProper_eq`, integrality, normalization/integral morphisms,
  and Noetherianity; none states the requested combined existence theorem.
- `msearch.py leanfinder`, query “Integral Chow envelope proper surjective birational
  modification with reduced projective compactification”: eight hits, principally
  `IsIntegralHom` and normalization, plus `Scheme.RationalMap.ofFunctionField`;
  none provides the stated Chow envelope and compactification.
- `msearch.py loogle`, query `AlgebraicGeometry.ChowModification,
  AlgebraicGeometry.Scheme.functionField`: zero hits; the service reports unknown
  identifier `AlgebraicGeometry.ChowModification`, so this search is inconclusive
  about the upstream-only Chow API, which was inspected directly instead.
- `msearch.py grep`, query `Chow|chow|genericPoint.*Spec|functionField.*Spec`, subdirectory
  `AlgebraicGeometry`: eleven Mathlib hits on rational maps and generic-point/function-field
  lemmas, no integral Chow envelope theorem.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id, integral Chow,
  compactification, and generic field maps. No declaration carries this item id or
  the proposed declaration name. Existing `ChowModification.nonempty_data` lacks the
  integral refinement, reduced compactification, and explicit field compatibility.
  `Sheaf.AlgebraicGeometry.IntegralChowRelativelyAmple.exists_integral_chow_relatively_ample`
  is over a field and supplies an ample twist, not this arbitrary affine Noetherian-base
  compactification statement. Function-field and vanishing-ideal constructions already
  exist and have been reused. No duplicate definitions were introduced.

Validation: all compiler invocations use the prescribed `scompile.py` wrapper; final
compile and preflight results are recorded by the delivery wrapper. No statement fault
or STATEMENT-DISPUTED issue was found.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
