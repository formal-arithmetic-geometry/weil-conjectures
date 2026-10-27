## Worker report

The delivery states `AlgebraicGeometry.semiabelian_gm_extension_ample_reflection`
in `Sheaf.AlgebraicGeometry.SemiabelianGmExtensionAmpleReflection`. Its sole theorem
has proof `sorry`. It introduces no definitions and changes no mathematical statement.
The node's accepted seven-step proof is reproduced in the declaration docstring.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Base scheme: `{S : Scheme.{u}}`. Affine: `[IsAffine S]`. Integral:
  `[IsIntegral S]`, including nonemptiness. Locally Noetherian:
  `[IsLocallyNoetherian S]`; affineness already supplies `CompactSpace S`, so this
  is precisely the node's Noetherian condition. Normality is `hS`, which asserts
  `IsDomain` and `IsIntegrallyClosed` for every local ring `S.presheaf.stalk s`.
- Commutative S-group schemes: `E H : Grp (Over S)` with
  `[IsCommMonObj E.X]` and `[IsCommMonObj H.X]`. The bundled group objects include
  their actual identity, multiplication and inverse as S-morphisms and the group
  identities. There is no field-base specialization or substituted group law.
- Smoothness and separatedness: `[Smooth E.X.hom]`, `[IsSeparated E.X.hom]`,
  and the corresponding two instances for H. `IsSeparated` is the closed-diagonal
  predicate from Mathlib, using `IsClosedImmersion` from the recorded dependency.
- Finite presentation of E and H over S: `LocallyOfFinitePresentation` and
  `QuasiCompact` for both structure maps. Their required quasi-separatedness
  follows from the already stated separatedness; it is not omitted mathematically.
- Group homomorphism: `q : E ⟶ H`; morphisms in `Grp (Over S)` preserve the
  given multiplication and identity. Inversion compatibility follows from these
  identities and is not an independent restriction.
- Faithful flatness and finite presentation of q: `Flat`, `Surjective`,
  `LocallyOfFinitePresentation` and `QuasiCompact` for `q.hom.hom.left`.
  Quasi-separatedness follows from separatedness of E over S: q is separated
  because its composite with H's structure morphism is E's structure morphism
  (`IsSeparated.of_comp`), and separated implies quasi-separated.
- Multiplicative kernel: `j : relativeSplitTorus S 1 ⟶ E`. This is the actual
  rank-one split torus, with its Laurent Hopf group law, over S. The existing
  `StandardGroupSchemes.multiplicative` is restricted to a field, so the already
  landed arbitrary-base construction is used. In rank one, the group algebra
  on `Fin 1 → ℤ` is the Laurent algebra: the basis indexed by the function with
  value n corresponds to t^n, with multiplication, counit and antipode as specified.
  We add its existing node `def-sfb-relative-split-torus` to `stmt_deps` as permitted
  by brief-stage2 section 5 (STMT_DEPS MAY GAIN LANDED NODES).
- Scheme-theoretic kernel identification: `hkernel` is the pullback square in
  `Over S` of the actual q against the actual identity `η[H.X]`, with j as the
  inclusion and `toUnit` as the structural arrow to S. This identifies the full
  scheme-theoretic kernel, including infinitesimal test points. Since H is separated,
  its identity section is closed; base change makes j a closed immersion. An extra
  arbitrary kernel scheme or merely a pointwise kernel condition is not used.
- Exactness as fppf sheaves: `hepi` is `Presheaf.IsLocallySurjective` for
  `yoneda.map q.hom.hom` on `Scheme.fppfTopology.over S`. Together with hkernel
  it states the exact sequence in the node. This implies the equivalent displayed
  torsor description: pairs (u,v) with q(u)=q(v) have the unique difference v-u
  in the supplied kernel, functorially on every S-test scheme. The equivalent
  description is not added as another conclusion or imposed as a stronger assertion.
- Invertible module: `M : H.X.left.Modules` and `[M.IsInvertible]`, using the
  project's existing local-rank-one definition.
- Inversion symmetry: `hsymmetric` is
  `Nonempty ((Scheme.Modules.tensorPullback (ι[H.X]).left).obj M ≅ M)`.
  The inverse is the actual inverse of the given group object. Nonempty here
  expresses exactly existence of the asserted isomorphism, not a choice of data.
- Ample pullback: `hample` is absolute `Scheme.Modules.IsAmple E.X.left`
  for the existing explicit tensor pullback of M along q. Its required invertibility
  proof is supplied by `((invertible_pullback_tensor q.hom.hom.left).1 M).2`,
  not added as a hypothesis and not supplied by a new postponed lemma.
- Conclusion: `Scheme.Modules.IsAmple H.X.left M`, the same absolute ampleness
  predicate. There is no conclusion merely about individual fibres or relative
  ampleness. No cubical structure, norm hypothesis or properness is assumed.

Dependency declarations read and used (module, name):

- `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Noetherian`, `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, `IsIntegrallyClosed`, with
  `IsDomain` in the recorded inline normal-local-domain convention.
- `Mathlib.CategoryTheory.Monoidal.Grp`, `CategoryTheory.GrpObj`, `Grp`, and
  `MonObj.ι`; `Mathlib.CategoryTheory.Monoidal.Mon`, `IsCommMonObj`, `IsMonHom`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `Limits.pullback`,
  and the associated `IsPullback` square, used internally in `Over S`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `IsClosedImmersion`,
  through `Mathlib.AlgebraicGeometry.Morphisms.Separated`, `IsSeparated`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, `LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres`, `HasSemiabelianGeometricFibres`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`, `Surjective`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`,
  `StandardGroupSchemes.multiplicative` and `multiplicativeGroup` (field-base
  dependency imported; arbitrary-base Gm is its existing relative counterpart).
- `Sheaf.AlgebraicGeometry.RelativeSplitTorus`, `relativeSplitTorus`, at rank one.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`, `Scheme.fppfTopology`;
  `Mathlib.CategoryTheory.Sites.Over`, `GrothendieckTopology.over`;
  `Mathlib.CategoryTheory.Sites.LocallySurjective`, `Presheaf.IsLocallySurjective`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, `Scheme.Modules.IsInvertible`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, the public upstream
  `Scheme.Modules.tensorPullback`; the adjunction itself need not occur in the signature.
- `WeilConjectures.AlgebraicGeometry.Ample`, `Scheme.Modules.IsAmple`.
- `WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`,
  `Scheme.Modules.invertible_pullback_tensor`, for the existing invertibility proof.

The available statement/proof-dependency modules are imported. Two proof dependencies
have no Lean statement recorded: `lem-sfb-linearized-ample-eigen-affine-cover` and
`lem-sfb-group-affine-section-ampleness`. They are only proof inputs and do not
supply any notion needed to write this signature. Their full roles remain in the
docstring, ready for stage 3. No new or repaired dependency module is needed here.

Sources: the node explicitly labels Raynaud XI 1.11 as support for the field
abelian-quotient case, not a verbatim source for this relative assertion. Its PDF
is not present locally. I preserve that distinction and the WANTED status in the
module docstrings. I read Stacks `groupoids.tex`, `example-multiplicative-group`
(Tag 022U), which describes Gm over arbitrary schemes and its coordinate group law.
The current blueprint is `literature/blueprint/latest` (snapshot main-20261024).
The accepted node, including the essential symmetry correction reviewed by L on
2026-10-24, is the precise statement being formalized; no further correction is made.

Edge cases checked: an empty base is already excluded by integrality, exactly as
in the node. Identity sections over the nonempty base exclude empty E and H.
Semiabelian fibres of torus rank zero are allowed by the existing definition;
there is no positive-dimensional abelian quotient hypothesis. All characteristics
and arbitrary normal integral Noetherian affine bases remain admitted. H need not
be proper, and the split extension H times Gm is admitted. There is no chosen
section of q, no requirement that the extension split, and no trivialization of M.
The symmetry hypothesis is retained, so the known nonsymmetric counterexample
mentioned in the node's review is not silently reintroduced. All test schemes
and fields use the library's common `Scheme.{u}` universe, without an independent
smaller test universe. `autoImplicit` and `relaxedAutoImplicit` are false.

Searches actually run through msearch.py for Q18 and this item:

- LeanFinder: "A semiabelian group extension by the multiplicative group reflects
  ampleness of symmetric invertible sheaves over a normal affine base". Eight
  results, about affine limits, base-change/Picard constructions and relative Picard
  kernels; none states this geometric ampleness reflection theorem.
- Loogle: "AlgebraicGeometry.Scheme.Modules.IsAmple, CategoryTheory.GrpObj.ker,
  AlgebraicGeometry.RelativeGm". Zero results; the service reports unknown identifier
  `AlgebraicGeometry.Scheme.Modules.IsAmple`, so this is not evidence of absence
  from the project (the declaration was read directly in project source).
- Grep: "semiabelian|[Aa]mple.*[Tt]orsor|[Aa]mple.*[Mm]ultiplicative" in
  Mathlib/AlgebraicGeometry. Zero hits.
- LeanSearch: "Ampleness of a symmetric invertible sheaf descends along a
  multiplicative group extension of semiabelian schemes". Eight results concerning
  flat descent, relative Picard groups, ordinary group extensions and affine
  pullbacks; none states this theorem.
- Direct rg on lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json
  for `semiabelian`, `GmExtension`, `ample.*reflection`, `relativeSplitTorus`,
  multiplicative-group names, the node id, and the proposed declaration name.
  Found the field-only `SemiabelianAbelianQuotientAmpleReflection` (different
  hypotheses), the finite-surjective ampleness reflection theorem (different
  morphism), and the usable `relativeSplitTorus`. No existing statement of the
  assigned theorem was found. The node-id and proposed-name searches had zero hits.

Validation: the prescribed scompile.py compiled this file separately in sandbox
and library positions, with no errors or unexpected warnings (2.8 and 4.3 seconds).

## Second reading by Q18

I reopened the node, the written signature and the source definitions for this
second pass; no additional agent was started, as instructed. The maintainer's
independent mathematical review remains the external review of this delivery.

I checked the distinction between schemes and `Over S` group objects: q and j
are bundled homomorphisms, not unrestricted scheme maps. The hkernel square uses
the identity of H and the structural map of the actual rank-one relative torus.
Its upper-left object is precisely that torus, so no weaker image-only or
geometric-point-only kernel identification has replaced the statement.

I checked finite presentation against def-sbc-locally-finite-presentation: the
written QC binders are present on E, H and q. QS for the structure maps follows
from their separatedness, and QS for q follows by `IsSeparated.of_comp` and its
commutation with the structure maps. Affineness of S supplies its quasi-compactness;
there is no dropped Noetherian condition. The normality binder includes both
local domain and integral-closure conditions. Both geometric-fibre assumptions
are present, and the library permits torus rank zero.

I checked the line-module clauses directly: the inverse arrow belongs to H's
specified group structure; the tensor-pullback functor is the real tensor formula;
hsymmetric asks exactly for the isomorphism in the node. The input and output
both use the absolute IsAmple predicate, and the pullback's invertibility proof
comes from the recorded theorem rather than an extra assumption. The negative
scope clauses introduce no missing hypothesis. No mismatch requiring a statement
change was found. The only DAG change beyond lean is citing the already landed
arbitrary-base split-torus node needed for the rank-one group, with no new notion.
