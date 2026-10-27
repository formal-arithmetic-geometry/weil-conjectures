## Worker report

The module `Sheaf.AlgebraicGeometry.SemiabelianMultiplicationFppf` states
`AlgebraicGeometry.semiabelian_multiplication_fppf`, with one whole-proof `sorry`.
It defines no new notion. The informal statement, proof and proof dependencies
are unchanged. The statement dependencies gain five already recorded nodes:
`def-sfb-semiabelian-geometric-fibres`, `pqf-def-quasifinite`,
`def-pc-fppf-site`, `def-weil-pbc-fpqc-covering`, and `def-pc-fibre-product`.
These make explicit the existing notions actually used in the statement.

Hypothesis and conclusion correspondence:

- The base is `{S : Scheme.{u}} [IsIntegral S] [IsLocallyNoetherian S]`.
  Its local normal domains are exactly `hS : ∀ s : S,
  IsDomain (S.presheaf.stalk s) ∧ IsIntegrallyClosed (S.presheaf.stalk s)`.
- The specified group scheme and its actual S-group law are `G : Grp (Over S)`;
  commutativity is `[IsCommMonObj G.X]`. The bundled group contains multiplication,
  inverse, identity and their identities, all in the category of S-schemes.
- Smoothness and separatedness are `[Smooth G.X.hom] [IsSeparated G.X.hom]`.
  The latter means exactly that the diagonal is a closed immersion.
- Finite presentation of the structure morphism is
  `[LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]` together with
  quasi-separatedness already implied by the separatedness hypothesis. Thus this
  is the full finite-presentation hypothesis, not merely local finite presentation.
- `hG : HasSemiabelianGeometricFibres G` is the already landed exact-sequence
  definition. For every algebraically closed field in the scheme universe and
  every geometric point, it supplies a split torus, a proper smooth connected
  group A, the actual kernel square, and local surjectivity for the big fppf
  topology. Over the algebraically closed field connected smooth A is geometrically
  connected. The Laurent G_m and its rank-zero product are the shared constructions
  in StandardGroupSchemes and ToriMultiplicativeType, not private replacements.
- `d : ℕ` and `hd : 0 < d` represent precisely the integers d ≥ 1.
  `(𝟙 G.X ^ d).left` is the sum-of-d-copies map on the underlying scheme, with
  the power computed in the pointwise group law on morphisms to G.X. No arbitrary
  endomorphism or extra invertibility assumption is introduced.
- `Flat (𝟙 G.X ^ d).left` is stalkwise flatness by Mathlib's
  `Flat.iff_flat_stalkMap`; `Surjective ...` means surjectivity on points.
- `Scheme.Hom.IsQuasiFinite ...` is the project's Stacks quasi-finiteness predicate,
  which includes finite type. `Scheme.Hom.HasFiniteFibres ...` explicitly retains
  the node's finite-fibre clause. These two compatible clauses do not substitute
  Mathlib's weaker bare `LocallyQuasiFinite` predicate.
- `LocallyOfFinitePresentation ... ∧ QuasiCompact ... ∧ QuasiSeparated ...`
  is exactly finite presentation of multiplication.
- `Presieve.singleton ... ∈ Scheme.fppfPrecoverage G.X.left` and its fpqc counterpart
  assert the actual singleton coverings. Quasi-compactness is already asserted
  explicitly, so the node's faithfully-flat-quasi-compact description is retained.
- `∀ (a : ℕ), 0 < a → ∀ R : WidePullbackCone
  (fun _ : Fin a ↦ (𝟙 G.X ^ d)), IsLimit R → ...` ranges over precisely the
  a-fold relation schemes, including their common-value and projection arrows.
  These cones are in `Over S`; finite limits in this category exist. Consequently
  this universal form is nonvacuous and independent of a choice of limit object.
- The properties of the relation structure map are `Flat R.pt.hom`,
  `LocallyOfFinitePresentation R.pt.hom`, `QuasiCompact R.pt.hom`,
  `QuasiSeparated R.pt.hom`, and `IsLocallyNoetherian R.pt.left`.
- `∀ U : S.Opens, Nonempty (IsLimit ((Over.pullback U.ι).mapCone R))`
  says the actual restricted cone is still the relation limit. The pulled-back
  diagram consists of G_U and the restricted multiplication arrows; the image cone
  keeps all a projections and the common-value arrow. It therefore specifies the
  canonical identification by the universal property, rather than an unlabelled
  isomorphism of underlying schemes. `Nonempty` here encloses the unique universal
  property on a fixed actual cone, not the choice of any map or group structure.
- There is no conclusion of finiteness or etaleness of multiplication over S.

Dependency declarations read and used:

| Node | Module | Declaration |
| --- | --- | --- |
| def-pc-scheme | Mathlib.AlgebraicGeometry.Scheme | AlgebraicGeometry.Scheme, Scheme.Hom |
| def-pc-integral-scheme | Mathlib.AlgebraicGeometry.Properties | AlgebraicGeometry.IsIntegral |
| pqf-def-locnoeth | Mathlib.AlgebraicGeometry.Noetherian | AlgebraicGeometry.IsLocallyNoetherian |
| def-weil-pbc-normal-ring | Mathlib.RingTheory.IntegralClosure.IntegrallyClosed | IsIntegrallyClosed, IsDomain (normal-domain inline conjunction) |
| def-sbc-smooth-morphisms | Mathlib.AlgebraicGeometry.Morphisms.Smooth | AlgebraicGeometry.Smooth |
| def-sbc-locally-finite-presentation | Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation | AlgebraicGeometry.LocallyOfFinitePresentation |
| def-sfb-semiabelian-geometric-fibres | Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres | AlgebraicGeometry.HasSemiabelianGeometricFibres |
| pqf-def-quasifinite | WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism | Scheme.Hom.IsQuasiFinite, Scheme.Hom.HasFiniteFibres |
| def-pc-fppf-site | Mathlib.AlgebraicGeometry.Sites.Fpqc | Scheme.fppfTopology, Scheme.fppfPrecoverage |
| def-weil-pbc-fpqc-covering | Mathlib.AlgebraicGeometry.Sites.Fpqc | Scheme.fpqcPrecoverage |
| def-pc-fibre-product | Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback | CategoryTheory.Limits.pullback (finite iterates represented by WidePullbackCone) |

The module includes the recorded, stated proof-dependency modules with ordinary
imports, including abelian multiplication, finite local freeness, field-extension
fpqc covering, pointwise and fibrewise flatness, and quasi-finiteness. The two
proof dependencies `lem-sfb-finite-flat-homomorphism-extensions` and
`lem-sfb-scheme-quasifinite-at-base-change` have no recorded declaration yet and
are mentioned in the proof docstring rather than imported as nonexistent modules.

Edge cases checked before writing: d=1 gives the identity and all assertions;
d=0 is correctly excluded; d divisible by the residue characteristic remains
allowed (G_m has the non-etale power map, with monic free root algebra).
Rank-zero tori, zero-dimensional abelian quotient and the trivial group satisfy
the same hypotheses and conclusion. Toric rank may vary over S. The index a=1
has one leg and relation scheme G; a=0 is excluded exactly as in the node.
The empty open U gives the empty restricted relation scheme and its genuine
limit cone. S itself is nonempty by integrality; no unsupported empty base is
silently used. Every universe is explicitly bound and test fields use the
scheme's universe through the shared semiabelian definition.

Searches made (2026-10-24):

- msearch.py leanfinder: “Multiplication by a positive integer on a semiabelian
  scheme is flat surjective quasi finite of finite presentation”. Eight hits
  concerned flat/finite morphism permanence and affine-space structure maps;
  none was this statement.
- msearch.py leansearch: “Positive multiplication on semiabelian schemes is flat
  surjective quasi finite”. Eight hits concerned LocallyQuasiFinite, flatness,
  affine faithful flatness, flat monomorphisms and quotient maps; no match.
- msearch.py loogle: `"pow", "Grp"`. Seven hits included MonObj/GrpObj comp_zpow
  and Grp.Hom.hom_pow, confirming the existing pointwise multiplication interface;
  none asserted the geometric conclusion.
- msearch.py grep: `semiabelian|Semiabelian|SemiAbelian` in AlgebraicGeometry:
  zero Mathlib hits.
- rg with those semiabelian patterns in lean/WeilConjectures and lean/Sheaf:
  no upstream multiplication statement; Sheaf contains the shared
  SemiabelianGeometricFibres module and distinct extension/density results.
- rg for `lem-sfb-semiabelian-multiplication-fppf` in lean/WeilConjectures: no hits.
  rg for `semiabelian_multiplication_fppf|SemiabelianMultiplicationFppf` in both
  library roots and Mathlib: no existing declaration/module.
- dag/lean_names_upstream.json multiplication/semiabelian search: no matching
  multiplication theorem. The shared semiabelian-geometric-fibres node was read
  with its complete defining module and its torus/abelian dependency definitions.

Source: the locally missing original was read from Numdam's author monograph,
https://numdam.org/item/AST_1985__129__1_0.pdf . II the project server, printed p.53,
uses surjectivity, flatness and quasi-finiteness of multiplication for connected
semistable A, for all n ≥ 1. II 1.2.7, printed p.48, defines the semistable
fibres as extensions of abelian varieties by tori. II 3.3.3, printed pp.53–54,
uses descent through multiplication. The relation assertions are the explicitly
stated base-change/composition/universal-property consequences in this DAG node.
The latest blueprint direct-image proof was also read; this remains an auxiliary
node of the inherited semistable Picard chain, not a change to that unit.
No statement correction or disputed clause was needed.

Validation: scompile.py compiled both sandbox and actual library module cleanly
against the live server (2.5 s and 2.2 s in the first run). Final preflight and
per-file compilation are performed by deliver2.py.

## Second reading by NA

Author self-check only: the dispatcher forbids starting another agent; independent
review is the maintainer's delivery review. I reread the node and full signature
clause by clause. Finite presentation is encoded completely using the separated
structure map and the explicit three-property conjunction in the conclusion.
The relation schemes are limit cones in Over S, not products of the underlying
scheme over S with no equality condition. Open restriction preserves that fixed
cone, so retains the projections and the specified multiplication arrows. The
shared semiabelian definition was checked to require a genuine kernel square and
fppf local surjectivity, with the actual induced group laws. All eight node proof
steps appear in the theorem docstring. No mismatch or statement change found.
