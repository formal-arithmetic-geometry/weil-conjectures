## Worker report

Delivered module: `Sheaf.AlgebraicGeometry.NodalGraphConeBaseChange`. Main declaration:
`AlgebraicGeometry.GraphCone.NodalBaseChange.exists_nodalGraphCone_baseChange`.
It has the sole postponed proof in this module. `Family`, `Family.diagram`, `Square`,
and `System` are supporting interfaces for this node's simultaneous comparison and
coherence assertion; they introduce no competing conormal algebra, pullback, or Proj.
The node statement and dependencies are unchanged.

Sources read: Stacks `divisors.tex`, lemmas `lemma-conormal-algebra-functorial` and
`lemma-conormal-algebra-functorial-flat` (0634, 0635); `curves.tex`,
`lemma-etale-local-structure-nodal-family` (0CBY); `constructions.tex`,
`lemma-relative-proj-base-change` (01O3). Also read the current blueprint
`latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`sk-thm-sf-ctf-stability-direct-images.proof.md`. That current unit text uses
compactification and the established proper/open preservation results. The present
node is the inherited subsidiary graph-cone comparison, rather than the statement of
that unit; its existing source and accepted seven-step split are retained.

Hypotheses and objects, matched to the node:

* The schemes X and T, and f:X→T, are `Family.X`, `.T`, and `.f`.
  `Family.flat : Flat f` and `.lfp : LocallyOfFinitePresentation f` are exactly
  flatness and local finite presentation. Both are registered as instances.
* `Family.geometric` is verbatim the geometric-fibre hypothesis in the recorded
  `nodal_family_fitting_singular` signature: it quantifies over every algebraically
  closed field Ω in the scheme universe and every `Spec Ω ⟶ T`; it is conditional
  on nonemptiness, requires `.IsPureDimension 1`, and requires
  `IsGeometricOrdinaryDoublePoint Ω ... x` at every point outside the geometric
  fibre's relative smooth locus. The completed local ring and power-series notions
  are those used by this existing definition, not replacement hypotheses.
* `Family.diagram := singularDiagram F.f` uses the actual first Fitting ideal sheaf,
  its closed subscheme, its inclusion i, and the original f. Thus D is the actual
  scheme, including its nilpotents, rather than a reduced support or a supplied
  closed subset. The graph algebra is `(K.obj F.diagram).algebra` of the recorded
  `GraphCone.Construction`, not an independently chosen graded algebra.
* `Square E F` gives a base morphism `t`, the family projection `x`, and the centre
  projection `z`. Its `family : IsPullback x E.f F.f t` means that E is the base
  change of F. Its `centre : IsPullback z E.diagram.i F.diagram.i x` identifies the
  actual first-Fitting centre of E with the inverse image of that of F. Pasting
  with the family square gives D'=D×_T T'. Its commutativity also fixes z uniquely
  because the first-Fitting inclusion is a monomorphism.
* These squares are not extra existence assumptions: the FIRST conjunct of the main
  theorem gives such an E and square for EVERY `F`, `T'`, and `a:T'⟶F.T`, together
  with `E.T ≅ T'` and `E.X ≅ pullback F.f a`. Its three equations identify t, x,
  and the structural map with the requested base change. Allowing these canonical
  isomorphic cartesian presentations avoids excluding identity and iterated base
  changes merely because Lean chooses fibre products differently.
* There is no flatness, reducedness, finiteness, separatedness, or quasi-compactness
  hypothesis on `a`, nor any such additional hypothesis on the families.

Conclusions, matched clause by clause:

* The SECOND conjunct asserts `∀ K : Construction, Nonempty (System K)` for the
  recorded glued graph-cone construction. Thus the result applies to the algebras
  of the gluing dependency, with all their existing chart identifications and
  functoriality, rather than selecting unrelated algebras or arbitrary maps.
* `System.comparison s` is the existing
  `Scheme.GradedAlgebraData.PullbackData s.z (K.obj F.diagram).algebra
  (K.obj E.diagram).algebra`. It includes the canonical affine semilinear graded
  maps, restriction compatibility, and degreewise `IsBaseChange` along the actual
  structure-sheaf ring maps. In the affine-basis encoding of quasi-coherent graded
  algebras, this is exactly the isomorphism `z* G_F ≅ G_E`: `IsBaseChange` says the
  induced coefficient-tensor map is invertible in EVERY degree. It does not
  require the semilinear map G_F(V)→G_E(U) itself to be bijective, which would be
  false for a general base morphism.
* `System.representative` fixes that comparison on every original affine graph
  chart and every induced `ChartSquare`. The source class is the inverse image
  under the existing chart equivalence of `DirectSum.of ... n (Quotient.mk a)`.
  The target is the existing `q.pieceMap n a`, multiplied by the actual degree-zero
  image of an arbitrary scalar `r`. By `ChartSquare.pieceMap`, this is the class
  of the actual ambient pullback of a, so the formula is precisely
  `[a] tensor r ↦ r[g-sharp(a)]`. Pure tensors generate. This normalization,
  together with restrictions, characterizes the comparison, rather than merely
  asserting that some pullback isomorphism exists. The scalar compatibility of
  `PullbackData` and the gluing's `degreeZero` identify the degree-zero unit basis.
* `System.coordinateTensor` explicitly quantifies over EVERY commutative A and
  EVERY commutative A-algebra A'. Its source and target are the actual rings
  `A' ⊗[A] (MvPolynomial (Fin 2) A ⧸ (uv))` and
  `MvPolynomial (Fin 2) A' ⧸ (uv)`. It asserts an A'-algebra equivalence whose
  formula on an arbitrary polynomial representative p is
  `e(r tensor [p]) = [C(r) * map(algebraMap A A') p]`.
  In particular p=1 gives the degree-zero basis, and p=X(0)^n and X(1)^n give
  r tensor u^n ↦ r u^n and r tensor v^n ↦ r v^n for every positive n, including
  n=1 as required in the displayed coordinate formula. The graph comparison has
  this coordinate expression because `representative` fixes the SAME images of
  the homogeneous coordinate classes. The nodal chart dependency identifies those
  classes with u,v and gives their bases. There is no second choice of a graph
  comparison in the polynomial formula.
* `System.identity` identifies the comparison of an identity square with the
  actual graded restriction map. On equal affines it is the identity; after
  coefficient tensoring this is exactly the tensor-unit identification.
* `System.composition` says the direct affine map is the composite of the two
  successive maps, with explicit equations on t,x,z. Passing to coefficient
  tensors is the stated tensor-associativity formula
  c_(a∘b)=c_b∘b_D* c_a. It permits every cartesian presentation of the composite.
* `System.isomorphism` identifies the comparison for an isomorphism square with
  the EXISTING normalized `K.algebraMap`. `System.naturality` is the commuting
  square with two arbitrary isomorphisms of families and the given base changes.
* For each s, the actual required Proj isomorphism is already the defined term
  `(system.comparison s).relProjIsoPullback`; this has type
  `Proj G_E ≅ pullback (Proj G_F ⟶ F.diagram.Z) s.z`.
  `PullbackData.relProjIsoPullback_hom_fst` identifies its first projection with
  `relProjComparison`, and `..._hom_snd` identifies its second with the actual
  structural map. This is the node's displayed order `(Proj_D G_F) ×_D D'`.
  `System.proj_identity`, `.proj_composition`, `.proj_isomorphism`, and
  `.proj_naturality` state the corresponding laws for the FIRST projections.
  The second projections are the structural maps, so the pullback universal
  property gives precisely all the full isomorphism coherence laws in the node.
  No arbitrary Proj isomorphisms, equality of schemes, or extra Proj models occur.

Dependency declarations read and used:

* `lem-trf-nodal-family-fitting-singular`:
  `Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular`,
  `AlgebraicGeometry.nodal_family_fitting_singular`; its geometric hypothesis is
  reused and its base-change conclusion supplies the centre square.
* `lem-sfb-graph-cone-gluing`: `Sheaf.AlgebraicGeometry.GraphConeGluing`,
  `AlgebraicGeometry.GraphCone.{Diagram,Chart,ChartSquare,Construction,Gluing,
  singularDiagram}`, with `Chart.ideal`, `ChartSquare.pieceMap`, the gluing's
  `chart`/`degreeZero`/restriction specifications and construction's normalized
  algebra and Proj functoriality. Read the entire module, including local charts
  and the existing branch normalization; none is privately duplicated.
* `def-pc-module-pullback`:
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`,
  `Scheme.Modules.tensorPullbackSectionAdjunction`, and the imported upstream
  `Scheme.Modules.tensorPullback`. Read the normalized unit, identity and
  composition signatures. The affine-basis tensor encoding is supplied by the
  existing `GradedRingHom.IsGradedBaseChangeAlong`, not a different pullback.
* `def-pc-fibre-product` and `def-weil-geometric-fibre`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`; all geometric fibres are
  schemes, with the scheme category explicitly fixed where required.
* `def-nagata-relative-proj`:
  `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`,
  `Scheme.GradedAlgebraData`, `.relProj`, `.relProjHom`, `.relProjι`.
  Read the affine-basis definition and Basic's gluing. The comparison interface
  and canonical isomorphism come from `RelativeProj.BaseChange`,
  `Scheme.GradedAlgebraData.PullbackData`, `.relProjComparison`, `.isPullback`,
  `.relProjIsoPullback`, and its two projection identities. Read their full
  signatures, as well as `GradedRingHom.IsGradedBaseChangeAlong` and its
  degreewise `IsBaseChange` definition.
* `def-weil-flat-morphism`, `def-sbc-locally-finite-presentation`,
  `def-sbc-smooth-morphisms`: Mathlib's
  `AlgebraicGeometry.{Flat,LocallyOfFinitePresentation,Smooth}` in the recorded
  morphism modules. `smoothLocus` appears in the geometric condition.
* `def-weil-pure-dimension`: `Sheaf.AlgebraicGeometry.PureDimension`,
  `Scheme.IsPureDimension`; read its irreducible-component definition, including
  the empty-scheme convention.
* `def-weil-pbc-adic-completion` and
  `def-weil-pbc-multivariate-power-series`: Mathlib's `AdicCompletion` and
  `MvPowerSeries`, in the recorded Basic modules. They occur through the reused
  `IsGeometricOrdinaryDoublePoint`, read in
  `Sheaf.AlgebraicGeometry.ProjectiveNodalTower`.
* `def-trf-first-fitting-singular-subscheme`:
  `Sheaf.AlgebraicGeometry.FirstFittingSingularSubscheme`,
  `Scheme.firstFittingIdealSheaf`, `.firstFittingSingularSubscheme`; read the
  affine Fitting characterization and the uniquely characterized construction.

The module imports the available proof-dependency modules for the general conormal
comparison, affine module-pullback sections, fpqc/etale comparison, flat-cover module
isomorphism reflection, relative Proj functoriality/base change, and etale precoverage
base change. The permanence results and affine Proj definitions are already public
through these imports and the statement imports. The proof-only node
`lem-sfb-nodal-graph-cone-chart` has no recorded Lean declaration or module on the
read base; accordingly no nonexistent import is added. Its proof is not used to
construct any definition here: it is only needed for the postponed theorem's proof.
There are no missing statement interfaces and no dependency modules in this delivery.

Edge cases checked before finalizing:

* Empty X or an entirely smooth family: D is empty and all statements concern
  its actual graded algebra and empty Proj. No nonempty-D assumption is introduced.
* Empty geometric fibres are expressly allowed by `Family.geometric`.
* Nonflat specialization `uv=t` over k[t], with t sent to zero: the split-node
  algebra is k[u,v]/(uv) on both sides. A general associated graded algebra need
  not commute with this specialization, which is why the statement retains nodality.
* Nonreduced base change t=s²: D' is Spec k[s]/(s²), not its reduction; the formula
  is still coefficientwise and the inverse on 1,u^n,v^n is unchanged.
* Zero coefficient ring and arbitrary positive characteristic, including 2:
  the polynomial tensor statement needs no nonzero assumption or division.
* Degree zero, n=1, and arbitrary positive n: the representative formula quantifies
  over ALL n, and the polynomial formula specializes to the stated coordinate powers.
* Identity and composite base changes, including isomorphic cartesian presentations:
  separate algebra and Proj laws are included, with all projection equations.
* All schemes, geometric coefficient fields and affine coefficient rings use the
  same explicit universe u as the recorded dependencies. No site-universe equality,
  quasi-compactness, or restriction on the base map is imposed.

Searches actually run:

* `msearch.py ... leanfinder`, query: “The graph conormal graded algebra of a nodal
  curve commutes with arbitrary nonflat base change with identity and composition
  coherence”. Eight hits: standard-smooth/formally-smooth base-change lemmas,
  WeierstrassCurve.map_baseChange, a cotangent-complex base-change identity, and a
  Proj chart pullback identity. None states this nodal graph comparison.
* `msearch.py ... loogle`, query: `"associatedGraded", "baseChange"`.
  Successful search, zero hits.
* `msearch.py ... grep`, query:
  `conormal.*base[Cc]hange|nodal|graphCone`, subdirectory `AlgebraicGeometry`.
  Successful search, zero Mathlib hits.
* `rg -n 'lem-sfb-nodal-graph-cone-base-change|graphCone|nodal.*[Bb]aseChange'`
  over both `lean/WeilConjectures` and `lean/Sheaf`: found the existing graph-cone
  gluing theorem and singular-locus base-change helpers, not this theorem.
* Further `rg` for split-node/nodal-chart declarations found completion, nodal-chart
  and binomial blowup modules, not a graded graph-cone base-change/coherence theorem.
  The binomial blowup ring presentations describe different centre blowups;
  the coordinate formula here uses existing Mathlib polynomial/quotient/tensor types
  directly and introduces no new ring construction.

Validation: the delivered module compiled in both wrapper sandbox mode and its actual
library module mode through `scompile.py Q158 lem-sfb-nodal-graph-cone-base-change`.
No errors or non-sorry warnings. No `#check` commands remain. `autoImplicit` is false;
all object, variable and universe binders are explicit. All source writes are confined
to this delivery sandbox; the read-only repository and live library were not edited.
No statement correction, STATEMENT-DISPUTED flag, new nodes, or dependency repairs.

## Second reading by Q158

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
