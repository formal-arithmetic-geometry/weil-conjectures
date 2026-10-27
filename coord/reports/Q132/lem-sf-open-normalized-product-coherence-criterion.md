## Worker report

Module: `Sheaf.SixFunctors.OpenNormalizedProductCoherence`.
Main declaration:
`AlgebraicGeometry.ProEtale.OpenExternalTensor.NormalizedProduct.coherence`.
This is a stage-2 statement with exactly one postponed theorem, `coherence`.
The three auxiliary definitions have actual bodies: the normalization predicate
and the two pastings of the supplied isomorphisms. No theorem is proved.
No statement correction, disputed statement, or new node is needed.

Hypothesis and clause correspondence:

- Finite commutative A: section binders `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  This is the published fixed-scalar presentation and size convention. `FiniteD A V`
  is the ordinary unbounded derived category of constant-A module sheaves on the
  small pro-etale site, with no constructibility, boundedness or Tor restriction.
- Arbitrary schemes over B: `B : Scheme.{u}` and `a : Xb ⟶ B`, `b : Yb ⟶ B`,
  `c : Wb ⟶ B`. The source schemes' structure maps are the composites with j,k,l.
  No finite-type, separatedness, quasi-compactness, or field condition is present.
- The three open immersions: explicitly bound `j`, `k`, `l`, with their three
  `IsOpenImmersion` instances. `Diagram` records their actual product open maps
  and the two canonical open factorizations, not arbitrary tensor comparisons.
- Z and T for each binary pair are `Tb₁₂,T₁₂`, `Tb₂₃,T₂₃`, and the common triple
  cones `Tb,T`. `_bar₁₂`, `_inner₁₂`, `_bar₂₃`, `_inner₂₃`, `_barL`, `_innerL`,
  `_barR`, `_innerR` are exactly the eight product universal properties over B.
  Arbitrary choices of limit cones are allowed. `t : Triple ...` identifies the
  two iterated products on the same total cone by their six projection equations
  and the equality of total open maps. This represents the node's canonical
  identification of iterated fibre products. Choosing these cones and their
  canonical intermediate opens introduces no extra geometric restriction.
- The arbitrary inputs are `K : FiniteD A X`, `L : FiniteD A Y`, `M : FiniteD A W`.
- The binary objects H and D are precisely the published `ambient A d K L` and
  `inside A d K L`: tensor of projection pullbacks of j!K,k!L and of K,L.
  The triple objects are the existing left-bracketed `tripleAmbient` and
  `tripleInside`; their composed projection pullbacks are canonically the
  direct projections in the node.
- The four independently supplied isomorphisms are `e₁₂`, `e₂₃`, `eL`, `eR`.
  Their types use exactly (K,L), (L,M), (inside₁₂,M), (K,inside₂₃).
  No formula or naturality hypothesis is imposed on them.
- The four normalization hypotheses are `_h₁₂`, `_h₂₃`, `_hL`, `_hR` using
  `IsNormalized`. The existing `restriction` is the forward identification
  D → u*H obtained from the two open units and inverse tensor comparison, i.e.
  r⁻¹ in the node. Thus `restriction ≫ pull.map e.hom = adj.unit.app D` is exactly
  u*e = r ≫ eta in Lean composition order. The open units are invertible by the
  cited normalization theorem; the equivalence does not add a hypothesis.
- F is `leftPaste`: inverse tensor/pullback comparison, pullback of e₁₂ tensored
  with identity, eL, then extension of the tensor/pullback comparison identifying
  its target with the prescribed left-bracketed D₃.
- G is `rightPaste`: the existing `outerAssociator`, pullback of e₂₃ tensored
  with identity, eR, extension of `innerAssociator`, and `shriekCongr` for the
  equality of the two product open maps. The existing associators use precisely
  pullComp, square, tensorPullIso and the native derived associator, with no
  permutation or sign. The intermediate coefficient objects are arbitrary.
  The supplied outer product comparisons already target the total open
  extension, so there is no iterated shriek left to compose in F or G. Any
  factorized presentation is identified by the recorded unique-left-adjoint
  compositor `FiniteOpenProduct.comp`, as explained in the proof docstring.
- The first two conclusion conjuncts are `IsIso (leftPaste ...)` and
  `IsIso (rightPaste ...)`.
- The next two are the separate equations
  `tripleRestriction ≫ pull.map leftPaste = adj.unit.app tripleInside` and the
  identical equation for rightPaste. These express v*F=v*G=identity after
  exactly the specified source identification and target open unit. The
  existing `tripleRestriction` contains only projection comparisons, tensor
  comparisons and the three section-normalized open units, and neither F nor G.
- The fifth conjunct quantifies over every `D' : FiniteD A T` and asserts
  `Function.Injective (fun h : tripleAmbient ... ⟶ (finiteShriek A dL.u).obj D' =>
  (FiniteOpenProduct.pull A dL.u).map h)`. Its source is precisely H₃. It makes
  no faithfulness assertion for an arbitrary ambient source.
- The last conjunct is equality of the actual morphisms `leftPaste = rightPaste`.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteOpenProductSwap`: `WeilConjectures.FiniteOpenProduct.tensor`,
  `tensorMap`, `tensorIsoMap`, `pull`, `pullComp`, `tensorPullIso`, `adj`, `comp`,
  `square`, `pullCongr`, `composeEq`; their definitions use the existing exact
  inverse image, native K-flat derived tensor, section adjunction and its unique
  left-adjoint compositor. This is the recorded statement prerequisite.
- `Sheaf.SixFunctors.OpenExternalTensorNormalization`: the coefficient-free
  `Diagram` and `Triple`, recorded by the already landed definition node
  `def-sf-open-external-product-diagrams`. That node is added to stmt_deps as
  authorized for already landed definition nodes. The module also supplies
  `ambient`, `inside`, `restriction`, `tripleAmbient`, `tripleInside`,
  `tripleRestriction`, `outerAssociator`, `innerAssociator`, `shriekCongr`,
  `proetAssociator`; each body and signature was read. These are reused, not
  redefined. Its theorem `finite_open_external_tensor_normalization` is NOT an
  input: it only concerns the specific canonical comparisons in a narrower
  six-functor setting. Its `tripleLeft` and `tripleRight` hardwire that canonical
  comparison and therefore cannot encode four arbitrary supplied isomorphisms.
  Import-cycle note for the maintainer: this module currently does not import
  the new criterion; a later proof-only back-import from that same module must
  be omitted or its existing helper data factored out before adding that import.
- Proof imports follow all recorded proof dependencies: `Adjunction.comp` and
  its component unit formula in `Mathlib.CategoryTheory.Adjunction.Basic`;
  `CategoryTheory.unit_conjugateEquiv_symm` in `Mathlib.CategoryTheory.Adjunction.Mates`;
  `SheafOfModules.openTensorNormalization` in `Sheaf.SixFunctors.OpenTensorNormalization`;
  `CategoryTheory.RingedDerivedNative.complexConstraints` in
  `Sheaf.Algebra.Homology.RingedTensorComplexConstraints`;
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`
  in `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`;
  `SheafOfModules.site_derived_tensor_descent_independentCoefficients` in
  `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
  They are plain proof imports. The module/declaration records, source signatures
  and docstrings were read. The theorem docstring carries all five proof steps.

Edge cases checked before writing: empty opens (the relevant extensions are zero),
identity opens (all units become the standard identity identifications), zero input
objects and the zero ring (allowed by CommRing and Finite), arbitrary unbounded
complexes, characteristic two, and odd cohomological degrees. Associativity does
not permute factors and contributes no Koszul sign. The injectivity assertion is
restricted to the supported triple source; it does not claim a false general
faithfulness of open restriction. No edge case requires an extra hypothesis.

Searches (all through prescribed tools or read-only rg):

- msearch leanfinder: "Two bracketings of normalized open immersion external
  derived tensor product comparisons agree by restriction". Eight hits, mostly
  Scheme.Modules.restrictFunctorComp and open-immersion section equations; no
  matching theorem for arbitrary normalized supplied isomorphisms.
- msearch loogle: "CategoryTheory.Adjunction, CategoryTheory.MonoidalCategory.associator".
  Zero hits; the latter guessed identifier is unknown. The existing project's
  `proetAssociator` and its full body were then read directly.
- msearch grep, CategoryTheory: "normalized.*product|product.*coherence|externalProduct.*assoc".
  Six hits in DayConvolution, none the normalized derived open product criterion.
- msearch leansearch: "Normalized external products of extensions by zero have
  associative triple pasting by injectivity of restriction". Eight hits on Ext
  associativity, generic composition and products with zero; no match.
- rg over lean/WeilConjectures and lean/Sheaf for normalized product, triple pasting,
  triple product coherence and external associativity; rg of the exact item id in
  WeilConjectures: no existing theorem for this criterion. Found the useful
  existing triple constructions in OpenExternalTensorNormalization and the
  semilinear analogue; neither states the conditional four-isomorphism criterion.
- rg over dag/nodes for OpenExternalTensor.Diagram/Triple and tripleAmbient:
  found the existing definition-node owner def-sf-open-external-product-diagrams,
  used directly. `tools/blueprint_refs.py search "triple open product"`: 0 hits.
- Read the current source in literature/blueprint/latest, clause (ii) of
  lem-sf-kunneth-coherence.proof.md, and literature/blueprint/COMMITS.txt, not an
  obsolete blueprint snapshot. This node is the open-product refinement, not
  the unit's own statement.

Validation: prescribed scompile.py compiled the same file in sandbox mode (4.7 s)
and library mode (5.7 s) on the server, with no diagnostics. All section variables
and universe u are explicitly bound; autoImplicit is disabled. Dry-run and delivery
results are appended below after running deliver2.py.

## Second reading by Q132

A separate pass reread the node and the completed source, checking especially
that the four isomorphisms remain independent inputs, all four normalizations are
present, both restriction identities use the same pre-existing tripleRestriction,
and injectivity quantifies over all D' but only this triple source. Checked each
of the eight product cones and all seven Triple equations against the two
bracketings; no scheme or coefficient hypothesis was added. Checked that the
right pasting ends in the same v!D₃ as the left pasting, including the transport
of equal product open maps. Checked that all new definitions contain actual
composites and the sole theorem proof is sorry. No mismatch was found or silently
corrected. This is a worker self-audit; the maintainer's independent review remains
the independent reading required by the dispatch workflow, and no other agent was
started under this brief.

Delivery validation: deliver2.py --no-push returned OK, commit a2acfe32569;
server preflight and all per-file compilation checks passed.
