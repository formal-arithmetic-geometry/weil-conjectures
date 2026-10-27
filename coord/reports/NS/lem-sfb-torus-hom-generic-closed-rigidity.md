## Worker report

The module `Sheaf.AlgebraicGeometry.TorusHomGenericClosedRigidity` states
`AlgebraicGeometry.torusHom_generic_closed_rigidity`. It introduces no definitions;
the theorem has exactly one whole-proof `sorry`.

The node-to-Lean correspondence is as follows:

- Scheme base: `{S : Scheme.{u}}`.
- Integral and locally Noetherian: `[IsIntegral S] [IsLocallyNoetherian S]`.
- Normal: `hnormal` says every stalk is an integrally closed domain, using
  `IsDomain` and `IsIntegrallyClosed`, the recorded normal-ring convention.
  For an integral scheme this is precisely normality; no global affineness is assumed.
- The generic point eta is `genericPoint S`; integrality supplies its existence
  and uniqueness. No arbitrary point or dense open replaces it.
- P and G are group schemes over S: `(P G : Grp (Over S))`. Their actual group
  structures are bundled and their commutativity is `[IsCommMonObj P.X]` and
  `[IsCommMonObj G.X]`.
- P is smooth and affine: `[Smooth P.X.hom] [IsAffineHom P.X.hom]`.
- P is of finite presentation: the three classes
  `LocallyOfFinitePresentation P.X.hom`, `QuasiCompact P.X.hom`, and
  `QuasiSeparated P.X.hom`, exactly the recorded scheme conventions.
- The torus splitting condition is `hP : IsRelativeTorus P.X`, which specifies
  an actual fppf cover and group-valued functor isomorphisms to finite products
  of units. Its finite ranks may differ among charts; on the integral, hence
  connected, base they give a constant rank. Rank zero is included.
- G is smooth and separated: `[Smooth G.X.hom] [IsSeparated G.X.hom]`.
- G is of finite presentation: the same three classes on `G.X.hom`.
- Semiabelian geometric fibres: `hG : HasSemiabelianGeometricFibres G`, using
  exactly the published definition and its induced group laws.
- The already given S-group homomorphism is `(f : P ⟶ G)`. Its underlying
  arrow in `Over S` is `f.hom.hom`, and its scheme arrow is `f.hom.hom.left`.
  Morphisms in `Grp` preserve the specified multiplication and identity.
- The generic map is the actual canonical base change
  `((Over.pullback (S.fromSpecResidueField (genericPoint S))).map f.hom.hom).left`.
  `hgeneric` asserts `IsClosedImmersion` of that map.
- The conclusion is `IsClosedImmersion f.hom.hom.left`, for the original map.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  together with `IsDomain` on stalks (normal-ring inline convention).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.Grp` and `GrpObj`;
  `Mathlib.CategoryTheory.Monoidal.Mon`: `IsMonHom`, `IsCommMonObj`.
  The same group-object interface works in `Over S` for arbitrary S.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- Scheme-convention leaves `IsSeparated`, `QuasiCompact`, `QuasiSeparated`,
  and `IsAffineHom` in their Mathlib morphism modules.
- `Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres`:
  `AlgebraicGeometry.HasSemiabelianGeometricFibres`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: its documented
  scheme/morphism base-change interface `CategoryTheory.Over.pullback`,
  defined in `Mathlib.CategoryTheory.Comma.Over.Pullback`. The module was read
  in full, including `baseChange_morphism_projections` and `baseChange_fiber`.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `MultiplicativeType.splitTorus`, used by the geometric-fibre definition;
  its field-only `IsTorus` is not applied to the general base S.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`:
  `StandardGroupSchemes.multiplicative`, read through its recorded split-torus use.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` and
  `Scheme.fppfTopology`, used by the two published definitions above.
- Added the already landed node `def-sfb-relative-torus` to `stmt_deps` and imported
  its module `Sheaf.AlgebraicGeometry.RelativeTorus`, using `IsRelativeTorus`.
  This avoids recreating the general-base torus notion from field-only terminology.

The available proof-dependency modules are imported privately. In particular,
`AlgebraicGeometry.splitLocalSpecialKernelLifting` and `AlgebraicGeometry.relative_torus_monomorphism_closed`
were read in full. The four-step proof docstring preserves the accepted argument:
local splitting and kernel lifting; generic detection using the group-algebra basis
and field-extension injectivity; the affine augmentation-ideal Nakayama argument;
and pointwise monicity on every test scheme followed by relative torus closedness.

Edge cases checked: the empty base is excluded by integrality, exactly as in the
node; positive-dimensional and non-affine bases are allowed; no quasi-compactness
of S is imposed. Rank zero is permitted and gives the closed unit section of the
separated target. A field base makes the generic condition the same closedness
condition up to canonical base-change isomorphisms. No restriction on characteristic
or perfectness is present. Non-split tori are included via fppf splitting. Finite
nonreduced kernels in characteristic p are not discarded: the hypothesis and
conclusion are scheme-theoretic closed immersions, and the proof docstring retains
the group-algebra basis argument. All test fields in the published geometric-fibre
predicate share the scheme universe u; there is no independent smaller universe.

Searches (2026-10-24):

- `msearch.py ... leanfinder` with “A homomorphism from a torus to a semiabelian
  scheme over a normal integral locally Noetherian base is a closed immersion if
  its generic fibre is a closed immersion”: eight results, all general closed
  immersion definitions/criteria (including `IsClosedImmersion`,
  `of_isPreimmersion`, `hasAffineProperty`, `isClosedEmbedding`), no exact match.
- `msearch.py ... leansearch` with “Generic injectivity of a torus homomorphism
  to a semiabelian scheme implies closed immersion”: eight general closed
  immersion results, no torus/generic rigidity statement.
- `msearch.py ... loogle` with
  `AlgebraicGeometry.IsClosedImmersion, AlgebraicGeometry.IsIntegral`: zero hits.
- `msearch.py ... grep` with `torus|semiabelian|multiplicative.type`, subdirectory
  `AlgebraicGeometry`: zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for torus/closed and torus/generic
  in both orders: no exact theorem; found the relative-torus definition, the
  monomorphism theorem, and the complete-local lifting theorem. The latter
  assumptions and conclusion differ from the present theorem.
- `rg` for the item id in `lean/WeilConjectures`: no match. Searched DAG nodes
  and read `def-sfb-relative-torus`, already landed, rather than adding a copy.

Source reading: the latest blueprint unit
`sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` was read; this is a
supporting lemma, not its own unit statement. Lan's online text was opened at
section 3.3.1 (printed p.69, PDF p.83), including Propositions the project server and the project server:
https://www.kwlan.org/articles/cpt-PEL-type-thesis-revision-dense.pdf .
Those propositions give extension and torus-closure results; the present
already-given-map consequence retains the node's independent local-kernel proof.

Validation: the required `scompile.py NS lem-sfb-torus-hom-generic-closed-rigidity`
run accepted the delivered module in both sandbox and library modes, with no
errors or unexpected warnings.

No statement correction, new node, dependency repair, or disputed statement.

## Second reading by NS

This is the author's second reading; the maintainer supplies the independent review.
Reopened the node and module together and checked each binder: S is integral,
locally Noetherian and normal at all stalks; P and G have the actual commutative
group structures over S; all smoothness, affineness, separatedness and finite-
presentation assumptions occur on the structure maps specified by the node.
The splitting predicate is the already landed general-base predicate, not the
field-only `MultiplicativeType.IsTorus`. Its rank-zero case and fppf group-functor
isomorphisms agree with the statement. G's geometric-fibre predicate uses the
same bundled G. The generic-fibre hypothesis pulls back the given f itself
along the residue-field map at the unique generic point. The conclusion is
closedness of that same original f; no existential extension or abstract image
replaces it. No added flatness, monicity, splitness, properness or finite-type-base
hypothesis occurs. The explicit quasi-compact/quasi-separated assumptions are
exactly the finite-presentation convention. No mismatch found. Only `lean` and
the addition of the existing relative-torus statement dependency change in the node.
