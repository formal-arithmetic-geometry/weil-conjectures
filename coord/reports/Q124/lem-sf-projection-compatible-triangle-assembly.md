## Worker report

Module: `Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly`.
Main declaration: `AlgebraicGeometry.ProEtale.ProjectionTriangleAssembly.projectionCompatibleTriangleAssembly`.
This delivery states the item, with one postponed theorem and concrete component definitions.
The theorem has the seven-step natural-language proof from the node in its docstring.
No statement correction or dependency-module repair is needed. The return repair adds the definition ownership node described below.

Hypothesis and clause correspondence:

- `F : FiniteFieldDatum` retains the characteristic prime, positive exponent, finite field,
  and fixed algebraic closure. `C : F.CoefficientDatum` supplies `C.l`, its primality and
  `C.different : C.l ≠ F.p`. `E`, `Field E`, `Algebra (Padic C.l) E`, and
  `FiniteDimensional (Padic C.l) E` are the finite coefficient extension.
  `Padic.coefficientExtensionRing C.l E (n + 1)` uses the dependency's valuation ring,
  chosen uniformizer and power quotient. Index `n : ℕ` represents every positive level.
  `ULift.{u+1}` is the existing fixed-scalar coefficient presentation, with the same ring.
- `_S : SixFunctorOperationDatum F C E (n+1) ...` is precisely the operation datum;
  there is no projection-invertibility datum or hypothesis. The finite ordinary operations
  are its normalized fixed-scalar realizations (the datum's finite adjunction, pullback,
  composition and support normalizations); all arrows are the existing concrete operations.
- `Spaces F` is the existing full category of schemes finite type over `F.k`, with all
  morphisms over that field. It imposes no separatedness on the structure maps.
  These are definitionally the `SixFunctorSpace F` of the recorded operation datum.
- The geometric clause quantifies over `f`, `i` and `s`, with `f` separated finite type,
  `i` open and `s` proper. The supplied compactification of `g` is exactly the factorization
  `g = i ≫ s`; quantifying over its actual factors covers every prescribed compactification.
  The existential `V W j b q p` supplies the triangle, with open `j,b`, proper `q,p`,
  `f = j ≫ q`, `b ≫ p = q ≫ i`, and the explicit scheme-level `IsPullback`.
  `V,W : Spaces F` records finite type of both new schemes. Their `IsNoetherian` and the
  three quasi-compact open maps are explicitly asserted. The remaining schemes are already
  finite type over the field, hence Noetherian and qcqs; no extra geometry is assumed.
  Properness of `p ≫ s` and the composite open immersion `j ≫ b` give the compactification
  of `gf`, with factorization following from the two displayed triangle equations.
- `FiniteAssembly` quantifies over every compatible Cartesian triangle in these spaces.
  It first equates the actual `CompactCompositionProjection.alpha` component with
  `canonical` on every object of the full `plusEtaleOrigin` category, retaining arbitrary
  ambient morphisms and arbitrary choices of origin witnesses.
- `candidateCompositor` is the independent `originCompositionAmbient`, conjugated by
  the existing `towerCandidateComparison` at the three indicated compactifications.
  `canonical` specializes it to the triangle's factorizations, using the existing
  `sixFunctorFactorCompactification`. It is not defined to be the raw triangle mate.
  Thus the first equality of `FiniteAssembly` is the required identification, not a
  tautological equality between two names for the same raw formula.
- In the second clause of `FiniteAssembly`, `DerivedCategory.boundedConstructible ... K`
  gives `K ∈ Dᵇ_c`, and `DerivedCategory.constructibleFiniteTor ... L` gives
  `L ∈ Dᵇ_ctf`. No finite Tor assumption is placed on `K`. These are the finite-level
  étale-origin presentations; `constructible_proEtale_origin` identifies them with the
  intrinsic constructible categories of the node. The existential proofs `hK,hT` assert
  that both `K` and `K ⊗ P_f P_g L` have bounded-below origin, rather than assuming it.
- `ProjectionEquation` spells out the two arrows of the displayed formula: first
  `PF_g`, then `g_!(PF_f)`, then the canonical compositor at `K ⊗ P_f P_g L`; versus
  canonical compositor at `K` tensor `1_L`, then `PF_gf`. Its final `trianglePull.hom`
  converts `P_f P_g L` to `P_gf L`. This puts both sides in the same actual Hom type and
  is equivalent to inserting the inverse identification on the right as in the node.
  `projection`, `ordinaryTensor`, `properOpenProjection` and `properOpenTensorIso`
  are the dependency's specified counit-defined projection and normalized open maps.
  Nothing is inverted to obtain a projection transformation.
- `Associativity (ordinary ...)` is the dependency's explicit three-cell grid equation,
  with its endpoint associators and equality transports. Together with the first clause
  of `FiniteAssembly` this says that the identification respects threefold parenthesizations.
  `IdentityCompatibility` records the two actual identity-square equations for `gamma`,
  with `sId` and `jId`; these are the proper/open unit normalizations used in the compositor.
  The independently defined canonical origin compositor already has its recorded unit laws.
- The final universal quantifiers over `Operations` and `Realizations` insert precisely
  the simultaneous ringed-diagram operations through `realizedSystems` and `realizedTensor`.
  `SystemEquation` quantifies over arbitrary `K,L` in the actual unbounded system categories
  and states `leftMap = rightMap` there, before evaluation or total limit. These maps retain
  every quotient transition and the specified intrinsic proper/open mate. Its associativity
  and identity clauses use the same system calculus. In particular this predicate does not
  assert `IsIso` of an arbitrary system mate, although the dependency's larger `TriangleLaws`
  predicate includes such an assertion; this delivery uses only its component formulas.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and `.CoefficientDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` (and its construction import):
  `Padic.coefficientExtensionRing`, `Padic.finite_coefficientExtensionRing`.
- `Sheaf.Paper.SixFunctorOperationDatum`: `WeilConjectures.SixFunctorOperationDatum`;
  its stages module gives the existing `sixFunctorFactorCompactification`.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`: `ExchangeProjectionStage` and its
  specified counit-based projection construction, specialized by the concrete finite maps.
- `Sheaf.Paper.QcqsCompactSupportRealization`: `sfQcqsCompactSupportRealization`, importing
  the recorded finite/integral/rational compact-support definitions. The present equations
  are at the finite and simultaneous-system levels; no higher-stage equation is added.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`: `originCompactSupport`,
  `originCompositionAmbient`, `originComposition` and its identity/associativity laws.
- `Sheaf.SixFunctors.CompositionProjectionMate`: `compact`, `projection`, `alpha`,
  `trianglePull`, `leftMap`, `rightMap`, `Associativity`, `ordinaryTensor`,
  `realizedSystems`, `realizedTensor`, `compositionProjectionMate`.
- `Sheaf.SixFunctors.AmbientProperOpenPasting`: `Spaces`, `geometry`, `Calculus`,
  `ordinary`, `Calculus.gamma`, `Calculus.sId`, `Calculus.jId`, and mapped composition instances.
- Replaced the returned theorem-only dependency by `def-sf-origin-candidate-comparison`,
  module `Sheaf.Paper.ProEtaleCompositionTowerNormalization`: only its concrete
  `towerCandidateComparison` is needed. The normalization theorem in that module has
  separated structure-map hypotheses and is not used as a theorem here.
- All other recorded proof-dependency modules are imported without `public`, except
  `CompactSupportSiteCoherence`, which is also publicly exposed by the operation datum.
  The proof plan names their role explicitly; none of the postponed steps is proved here.

Edge cases checked: `n=0` in the Lean index is exactly the source's level one, so no positive
level is excluded. Identity arrows and empty schemes are allowed by the geometric quantifiers.
Zero derived inputs and non-perfect bounded constructible `K` remain allowed. No absolute
separatedness is present. All object/coefficient/site universes are retained; `ModuleCat`
uses the existing `u+1` convention. System inputs have no boundedness, finite Tor, completion,
constructibility, or origin hypothesis. No faithfulness of evaluation is assumed.

Searches for an existing statement (2026-10-23):

- `msearch.py ... leanfinder "Compatible compactification triangle realizes canonical compact
  support composition and projection formula on etale origin derived inputs"`: eight hits,
  involving affine transition limits and related geometric projection equalities; no match.
- `msearch.py ... loogle "CategoryTheory.mateEquiv, AlgebraicGeometry.Compactification"`:
  zero hits (the Mathlib endpoint does not know the project compactification identifier).
- `msearch.py ... leansearch "Compactification composition projection formula derived sheaves"`:
  eight hits about structure sheaves, pullbacks and supports; no match.
- `msearch.py ... grep "originComposition|compatible.*[Tt]riangle" CategoryTheory`:
  one unrelated Mathlib triangulated-localization hit.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  no existing declaration of this item or of the chosen public declaration names.
  The item id occurs in the downstream `ProjectionIntegralCoherenceRealization` proof
  docstrings, not in a statement of this assembly. The nearest statement is the tower
  normalization node above, which requires separated structure maps and has no projection
  formula/system assembly conclusion. The mate dependency gives the raw formula but does
  not identify it with the canonical origin compositor. Neither is this item.

Validation: prescribed `scompile.py` compiled the delivered module both as sandbox module and
at its library module name, cleanly. Early elaboration failures came from typeclass keys for
underlying maps versus `geometry.map`; the final binders and explicit mapped-composition
proofs now use the dependency's exact interface. No compiler probes remain.

## Second reading by Q124

Repair self-check (2026-10-23): read the new definition node against the full existing
`towerCandidateComparison` declaration and both factors of its site-comparison chain.
Every parameter, the c-to-d direction, the full-origin domain and the canonical
fully faithful preimage construction agree. The item now cites the definition node
and no longer adds the separated-base normalization theorem as a statement dependency.
The existing Lean file and its mathematical signature remain byte-identical.

Fresh self-check of the node and completed file: the canonical comparison is independently
constructed, the Cartesian compatible triangle is existential rather than hypothesized, the
finite equation has precisely finite Tor on `L`, and the system equation has no invertibility
claim. The pullback transport direction and all three candidate compactifications were
checked against the displayed node equation and Stacks 0F7J. The geometric source is read
in `more-etale.tex`, lemma-shriek-composition, and the current blueprint proof's composition
sentence. The dispatcher explicitly prohibits starting another agent; this is a documented
self-check, with the independent maintainer reading to follow delivery.

## New nodes

`def-sf-origin-candidate-comparison` records the existing definition
`AlgebraicGeometry.ProEtale.towerCandidateComparison` in
`Sheaf.Paper.ProEtaleCompositionTowerNormalization` (line 191). No module is duplicated.
Its source is the current composition blueprint's “Independence and associativity”
paragraph. It conjugates the etale common-refinement comparison by the canonical
`compactSupportSiteComparison` maps, then takes `preimageIso` under precomposition
with the origin equivalence. The ring is finite commutative in `Type (u+1)`, schemes
are in universe `u`, the map is quasi-compact, and both candidates are supplied.
The node's exact signature has the surrounding explicit section parameter
`Λ : Type (u+1)` with `[CommRing Λ]`. There is no field or separated-structure-map
hypothesis and no normalization-theorem use. Its declarations list includes the
required existing helper.

LeanSearch and LeanFinder each returned eight unrelated Mathlib declarations; exact
queries and returned names are recorded in `mathlib_searches`. Prescribed Mathlib
grep and direct Mathlib rg found no match. Project rg found the existing helper and
three uses in its module. DAG rg found only the theorem node's helper listing;
`blueprint_refs.py search candidate` returned 25 candidates, none defining this
site-conjugated map. The related `def-trf-admissibility` owns a different realization
in its finite-field/coefficient context. The maintainer expressly requested ownership
of the general helper already used here, so this node reuses that exact declaration.
The known prerequisite closure has no route back to the item; unrelated inherited
missing references in the local DAG are left to the server's prescribed preflight.

## Return repair (H2, immutable head fb8e5eb1b0db)

The return identified the extra statement dependency on
`lem-trf-proetale-composition-tower-normalization`: only its plain helper definition
was used, with no definition node owning it. Added the requested existing:true node
with the exact module and declaration, and replaced that theorem id in the item's
`stmt_deps` by `def-sf-origin-candidate-comparison`. Mathematical statement, proof plan
and Lean source are unchanged. The saved packet first passed the required initial
dry run at 0f450770f47; this substantive ownership repair discharges the independent
review finding despite that earlier mechanical success.

Self-check: read the full helper signature and body, site-comparison factors and
Etale PlusιIso. Finiteness, quasi-compactness and both retained candidates match the
new node; the arrow runs from c to d. The construction uses no `.choose` or theorem
conclusion. Equal candidates, empty schemes and all isomorphic origin realizations
remain admitted. The original clause-by-clause self-check applies to the unchanged
Lean file. No other numbered return point was present.

Repair validation: prescribed `scompile.py` compiled the unchanged module at both its
sandbox and library names with no diagnostics. The repaired server dry run passed
preflight and compiled both the existing-declaration check and the delivered module
(commit 4427aad7457). Compared the sandbox node with the current read clone: only
`lean` and `stmt_deps` differ; the latter adds exactly the new definition node to the
base. Checked the theorem signature against its recorded text, and the new node's
citation set against its `stmt_deps`; both match exactly.
