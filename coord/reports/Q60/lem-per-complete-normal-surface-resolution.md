## Worker report

Recovered and repaired the saved statement module
`lean/Sheaf/DeligneLaumon/CompleteNormalSurfaceResolution.lean`.
It states `AlgebraicGeometry.exists_regular_proper_model_of_complete_normal_surface`
with one `sorry` proof and no new definitions. The mathematical node is unchanged.
The source is Stacks Project, `literature/stacks-project/resolve.tex`, Tag 0BGN,
`lemma-resolve-complete` (lines 3834–3954), together with `definition-resolution`
(lines 3702–3706). The source was read in full, including its degree induction.

Each hypothesis and conclusion has the following rendering:

- Commutative ring A: `(A : Type u) [CommRing A]`.
- Noetherian: `[IsNoetherianRing A]`.
- Normal domain: `[IsDomain A] [IsIntegrallyClosed A]`, exactly the normal-domain
  form specified by the recorded normal-ring dependency.
- Local ring and its named maximal ideal: `[IsLocalRing A]`, `(𝔪 : Ideal A)`,
  `[𝔪.IsMaximal]`, and `h𝔪 : 𝔪 = IsLocalRing.maximalIdeal A`. Naming 𝔪
  introduces no restriction: every local ring supplies that unique maximal ideal.
- Krull dimension two: `hdim : ringKrullDim A = (2 : WithBot ℕ∞)`.
- Complete for the maximal-ideal-adic topology: `hcomplete : IsAdicComplete 𝔪 A`.
- Integral scheme T exists: `∃ (T : Scheme.{u}) (_ : IsIntegral T)`; the dependent
  proof binder exposes the integral instance needed by the generic-point interface.
- Morphism to the affine spectrum: `(f : T ⟶ Spec (.of A))`.
- Proper morphism: `IsProper f`.
- Regular source: `IsRegularScheme T`, which includes local Noetherianity.
- f induces an isomorphism of function fields: there exists
  `hη : f (genericPoint T) = genericPoint (Spec (.of A))` and
  `IsIso (f.functionFieldMap hη)`. The actual generic stalk map is required.
  This is the integral-scheme function-field clause of def-sc-function-field,
  not a choice of an unrelated abstract field isomorphism.

Dependency declarations read and used (module, name):

- `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, `IsIntegrallyClosed`
  and its normal-domain encoding together with `IsDomain`.
- `Mathlib.RingTheory.KrullDimension.Basic`, `ringKrullDim`.
- `Mathlib.RingTheory.AdicCompletion.Basic`, `IsAdicComplete` (the named
  companion of `AdicCompletion` in this dependency's declarations).
- `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`, `AlgebraicGeometry.IsRegularScheme`.
- `Sheaf.AlgebraicGeometry.FunctionField`,
  `AlgebraicGeometry.Scheme.functionFieldOfComponents`; its docstring and node
  explicitly prescribe Mathlib `Scheme.functionField` for arbitrary integral schemes,
  which is the form used here.
- `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback`,
  `AlgebraicGeometry.Scheme.Hom.functionFieldMap`. This module is absent from the
  old local checkout; its full current source was read using the authorized
  `scompile.py --source` command. It is defined for arbitrary integral schemes,
  despite its module name, and is the generic stalk map induced by f.

All currently stated proof dependencies are imported without `public`; the full
10-step node proof, with its dependency ids, is included in the theorem docstring.
No missing proof prerequisite was promoted to an assumption in the statement.

Edge cases checked: dimension zero (fields) and dimension one (DVRs) are excluded
by the source's dimension-two premise; the zero ring is excluded by `IsDomain`.
The empty scheme cannot witness the conclusion because `IsIntegral T` includes
nonemptiness. Already regular A allows the identity resolution. There is no
characteristic restriction, perfectness hypothesis, separability assumption,
algebraically closed residue-field assumption or finite-type-over-a-field premise.
The model has the same universe as A, as do the published surface interfaces.
An abstract field isomorphism alone was rejected: a Frobenius morphism in positive
characteristic, or a constant morphism between schemes with abstractly isomorphic
function fields, need not induce that isomorphism. The final statement tests f itself.

Searches made on 2026-10-19 using the prescribed msearch.py wrapper:

- LeanFinder: "complete Noetherian normal local domain of dimension two admits a
  proper birational regular model". Eight hits, including dimension-one DVR TFAEs,
  elliptic good reduction and scheme normalization; none is a surface resolution.
- Loogle: "IsAdicComplete, IsIntegrallyClosed, IsRegularScheme". Zero hits;
  `IsRegularScheme` is not a Mathlib identifier (it is the published project predicate).
- grep: "complete.*normal.*surface|resolution.*singular". Zero Mathlib hits.
- LeanSearch: "resolution of singularities of complete normal local surfaces".
  Eight hits, including normalization morphisms and smooth-locus facts; no match.
- rg in the upstream WeilConjectures source and project lean/Sheaf for
  "complete.*normal.*surface|exists_regular_proper_model_of_complete_normal_surface|
  lem-per-complete-normal-surface-resolution". No declaration of this theorem;
  the parent ExcellentSurfaceDesingularization only references it in its proof plan.
- rg in Mathlib, upstream and lean/Sheaf for birational/function-field-map interfaces.
  The parent resolution module uses the published `functionFieldMap`, whose full
  signature was then read from the live source. No new definition is needed.
- The declaration name and blueprint id were also checked against
  dag/lean_names_upstream.json, with no duplicate found.

No statement dispute, node correction, new node or dependency repair is needed.
Only the item's lean record changes relative to the repository node.

Validation: prescribed scompile.py compiled both the sandbox file and its library
module (2.9 s and 2.8 s), with no diagnostics. All variables and universes are
explicitly bound and autoImplicit is false. The JSON signature was extracted
verbatim from `theorem` up to the proof delimiter `:=`; JSON uses indent 1 and a final newline.

## Second reading by Q60

The recovery worker read the previous worker's module, the node and all nine
statement dependency records, and checked their declaration signatures/docstrings.
The saved packet had no report. Its field-isomorphism clause was also too weak:
`Nonempty (functionFieldOfComponents T ≅ functionFieldOfComponents (Spec A))`
did not connect that isomorphism to f. This was replaced by the induced generic
stalk map being an isomorphism, using the already published upstream interface.
The integral proof was moved to a dependent existential binder so that this map
can be typed with T's integral instance. The Noetherian, domain, normal, local,
maximal-ideal, dimension and completeness hypotheses were retained. Properness,
regularity, integrality and the affine target all match the node clause by clause.
The brief proof summary was expanded to the node's complete ten-step proof plan;
all stated proof prerequisites were added as non-public imports. The repaired
module compiles cleanly. The node's mathematical statement is unchanged.
