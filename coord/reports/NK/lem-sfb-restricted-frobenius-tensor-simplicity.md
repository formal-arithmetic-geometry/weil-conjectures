## Worker report

Item: lem-sfb-restricted-frobenius-tensor-simplicity. Module:
`Sheaf.AlgebraicGeometry.GroupScheme.RestrictedFrobeniusTensorSimplicity`.
Main declaration:
`AlgebraicGeometry.RationalHighestWeight.restricted_frobenius_tensor_simplicity`.
Its sole proof is `sorry`, with the full four-step proof plan in the docstring.
`tensorPullbackCoaction` is an explicit linear map, with no postponed data or proof fields.

The TeX statement, proof and proof dependencies are unchanged. The sole added
statement dependency is the already landed `def-sfb-rational-highest-weight-data`;
brief-stage2 section 5 permits adding a landed definition used by the statement.
This supplies the exact existing simplicity and highest-weight notions. There are
no new nodes and no dependency modules. No statement correction or dispute arose.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Algebraically closed field F | `{F : Type u} [Field F] [IsAlgClosed F]` |
| Characteristic p > 0 | `(p : ℕ) [Fact p.Prime] [CharP F p]`; a field's positive characteristic is prime, so this is the same hypothesis and includes 2. |
| F-group schemes S, T, B and U, group homomorphisms | `Grp (Over (Spec (.of F)))` and morphisms in `Grp`; this is exactly the recorded `GrpObj` group-object interface, bundled. |
| S smooth, connected, affine, finite type, no nontrivial smooth connected solvable normal subgroup | `hS : IsSemisimpleGroupScheme S.X`. This existing predicate uses the terminating scheme-theoretic commutator series, not solvability of rational points. |
| Simply connected | `hsc`: every surjective homomorphism from a semisimple S' with finite central kernel is `IsIso`. Centrality is the displayed commuting equation for every commutative F-algebra A and all kernel and S' points. `IsFinite (GrpObj.ker g).hom` is the recorded finite group-scheme notion, equivalently finite-dimensional coordinates. |
| Chosen split maximal torus T in S | `iT`, `hT : ReductiveTorusCentralizer.IsMaximalTorus iT`, and `hsplit : ∃ r, Nonempty (T ≅ MultiplicativeType.splitTorus F r)`; rank 0 allowed. The maximal-torus predicate already includes the closed inclusion. |
| Borel B containing T | `iB`, `j`, `hB : IsBorelGroupScheme iB.hom.hom`, `hj : j ≫ iB = iT`. The Borel predicate is maximal smooth connected solvable closed subgroup. |
| U is the unipotent radical of B | `iU` and `hUclosed`, `hUnormal`, `hUsmooth`, `hUconnected`, `hUunipotent`, `hUmax`. These are exactly the radical specification from the recorded Borel-pair structure theorem. `hUmax` says every smooth connected normal unipotent closed subgroup factors through U. |
| Character lattice X, cocharacters, root datum, simple roots, coroots, integral pairing | Actual additive Hom groups to/from `Grp.mk (StandardGroupSchemes.multiplicative F)`, `Φ : Finset ...`, `P : RootDatum Φ ...`, `b : P.Base`, `[P.IsReduced]`. Simple roots are `b.support`; coroots are `P.coroot`; pairing is `P.toLinearMap`. `hroot` identifies roots with the actual characters, and `hpair` identifies pairing with the integer power of the identity of G_m. |
| Roots from Lie(S), positive roots from Lie(B) | `aS`, `aB`, `hconjS`, `hconjB` pin both torus actions to conjugation. `hweights` identifies Φ with exactly the nonzero character tangent weights of S. `hpositive` identifies positivity with the tangent weights of B. This uses full torus characters, not their differentials. |
| f is a surjective group-scheme homomorphism with finite scheme-theoretic kernel | `f : S ⟶ S`, `hfsurj : Surjective f.hom.hom.left`, `hfker : IsFinite (GrpObj.ker f.hom.hom).hom`. There is no separability or prime-to-p assumption. |
| f(T) contained in T and f(U) contained in U as scheme factorizations | `fT`, `hfT : fT ≫ iT = iT ≫ f`, `fU`, `hfU : fU ≫ iU ≫ iB = iU ≫ iB ≫ f`. Factoring a homomorphism through a subgroup inclusion automatically makes the factor a homomorphism; bundled factors therefore impose no additional condition. |
| Pullback on every torus character is multiplication by p | `hfchar : ∀ χ, fT ≫ χ = χ ^ p`. Multiplicative character powers are additive multiplication by p in X. |
| V and W arbitrary finite-dimensional F-vector spaces | Independent `{V : Type v}` and `{W : Type w}`, each with `[AddCommGroup] [Module F] [FiniteDimensional F]`. |
| Rational coactions | `cV`, `cW`, with `hcoassocV`, `hcounitV`, `hcoassocW`, `hcounitW`, using existing `HopfAction.Coassociative` and `HopfAction.Counital`. |
| Simple means nonzero with only zero and full coaction-stable subspaces | `hsimpleV : IsSimple cV`, `hsimpleW : IsSimple cW`, from the landed coaction definition. Stability is membership in the image of the tensor inclusion of a linear subspace. |
| U-invariants are a line, T acts on it by lambda or mu after every scalar extension | `hhighestV : HasHighestWeight cV iT (iU ≫ iB) lam.toMul` and `hhighestW` with `mu`. The predicate uses the coaction equalizer for U-invariants, finrank 1, and the exact character coaction on the whole line. A coaction identity is equivalent to the claimed identity after every F-algebra extension, including nonreduced ones. |
| lambda and mu dominant | `hdomV` and `hdomW`: nonnegative integer pairing with `P.coroot α` for each `α ∈ b.support`. |
| lambda is p-restricted | `hrestricted` gives pairing strictly below `(p : ℤ)` for each simple coroot; `hdomV` supplies its lower bound 0. There is no upper bound on mu. |
| f*W has exactly underlying vector space W and coaction (1 tensor f-sharp)cW | Inside `tensorPullbackCoaction`, `(coordinateMap f).toLinearMap.lTensor W ∘ₗ cW`. `coordinateMap` uses the actual morphism's `appTop`, not an unspecified algebra map. No copy, lift or change of scalars of W is used. |
| Diagonal coaction on V tensor f*W | `HopfAction.tensorCoefficients F (coordinateAlgebra S) F V W ∘ₗ TensorProduct.map cV ((coordinateMap f).toLinearMap.lTensor W ∘ₗ cW)`. On pure tensor expansions this is sum `(vi tensor wj) tensor (ai * f-sharp(bj))`, exactly the node's action formula. |
| The resulting tensor is a simple rational S-module | Conclusion gives `HopfAction.Coassociative`, `HopfAction.Counital`, and `IsSimple` for this exact constructed map. The first two make rationality explicit rather than relying on an unproved interpretation of a bare linear map. |

The affine typeclass binders for S, T and U expose structures already required by
semisimplicity, split-torus structure, and the closed radical subgroup. They do not
exclude cases. Commutativity witnesses for T and G_m likewise expose the intrinsic
structures needed for Hom-group addition. No finite-field model, special split-model
Frobenius, nonzero weight, positive semisimple rank or irreducibility of the root
system is assumed. None of the flag-quotient conclusions of the Borel structure
node is made a hypothesis.

Dependencies read and used:

- `def-weil-field`: Mathlib `Field`, `Algebra/Field/Defs.lean:180`; full signature and docstring read.
- `def-weil-algebraic-closure`: `IsAlgClosed` in `Mathlib.FieldTheory.IsAlgClosed.Basic:62`, the relevant component of its mathlib_match; the node does not require choosing an algebraic closure here.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj` and bundled `CategoryTheory.Grp`, `Mathlib.CategoryTheory.Monoidal.Grp`; the specialized documentation, subgroup predicates and kernel interface in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` were read. Finite means `AlgebraicGeometry.IsFinite` on the kernel's structure map.
- `lem-sfb-reductive-borel-pair-structure`: `AlgebraicGeometry.reductive_borel_pair_structure` and `AlgebraicGeometry.semisimpleGroupScheme_isReductive`, `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`. Full signatures/docstrings read. The statement's Borel, radical, conjugation and character-root interface is the same one used there.
- `def-sfb-rational-highest-weight-data`: `coordinateAlgebra`, `coordinateMap`, `IsStable`, `IsSimple`, `invariants`, `characterElement`, `HasHighestWeight`, `Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData`; full source and docstrings read. This module's existing instance exposes the canonical coordinate Hopf algebra.
- Supporting existing definitions (transitive imports): `IsSemisimpleGroupScheme`, `IsSolvableGroupScheme`, `GroupSchemeDerivedLength`, `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`; `IsBorelGroupScheme`, `Sheaf.AlgebraicGeometry.GroupScheme.Borel`; `ReductiveTorusCentralizer.IsMaximalTorus`, `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`; `HopfAction.Coassociative`, `HopfAction.Counital`, `HopfAction.tensorCoefficients`, `Sheaf.RingTheory.HopfActionModuleData`; Mathlib `RootDatum` and `RootPairing.Base`.
- Stated proof inputs imported without `public`: `AlgebraicGeometry.Smooth.geometricallyReduced`, `WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced`; `IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed`, `Mathlib.RepresentationTheory.AlgebraRepresentation.Basic`; `Module.Finite.toModuleEnd_moduleEnd_surjective`, `Mathlib.RingTheory.SimpleModule.Basic`. Full signatures and relevant section variables read.
- Unstated proof inputs `lem-sfb-scalar-p-isogeny-relative-frobenius` and `lem-sfb-restricted-module-infinitesimal-simplicity` have no lean record or Mathlib match in the read clone; they are proof dependencies only, not prerequisites for typing this statement. Their imports are omitted until those nodes are stated, as required by stage 2 rule 7. They remain named in the theorem's proof docstring.

Source and edge-case checks:

Read Milne's local PDF via pdftotext, especially 22.54--22.55 (printed pp.481--482)
and the full isogeny theorem 23.25 (pp.492--493). The former supplies restricted
infinitesimal simplicity and Steinberg tensor products; the latter gives uniqueness
up to inner torus automorphism used to handle the node's arbitrary scalar-p isogeny.
Jantzen II.3.16--3.17 is cited by the node but remains unavailable locally; it is not
claimed read. The proof docstring retains the node's direct tangent/matrix-unit
argument and injective-coordinate descent for arbitrary f.

Checked p=2 (no division by 2), lambda=0 or mu=0 (all pairings may vanish), a product
of simple groups (no irreducibility assumption), S=1 (rank-zero torus, empty Φ and
simple support, dominance and restriction vacuous), and dimension-one simple
modules (matrix-unit argument with d=1). Zero V or W is excluded exactly by the
node's simplicity hypotheses; the constructed map itself is defined even on zero
spaces. Nonreduced test algebras are retained by coaction invariants and the
all-algebras centrality condition. V and W have independent universes v and w;
no equality with the coefficient-field universe is imposed. The factorization
hypotheses constrain actual scheme morphisms and not just F-points.

Searches actually run (the wrapper log is searches.jsonl in the sandbox):

- msearch leanfinder: `Steinberg tensor product simplicity for a restricted highest weight rational module and a Frobenius pullback`. Eight hits: root-representation irreducibility, FDRep scalar-end/Schur statements and isotypic-component results. No rational algebraic-group Frobenius tensor simplicity theorem.
- msearch loogle: `"Frobenius", "Representation"`. Zero hits.
- msearch grep in Mathlib/RepresentationTheory: `Steinberg|frobeniusTwist|tensorCoaction`. Zero hits.
- msearch leansearch: `The diagonal coaction on the tensor product of rational algebraic group modules multiplies the coordinate Hopf algebra coefficients`. Eight hits, chiefly tensor coalgebra comultiplication and abstract monoid diagonal representations; none defines the requested rational pullback tensor coaction. Reused the project's `tensorCoefficients` instead of redefining coefficient multiplication.
- msearch leansearch: `Steinberg tensor product theorem simple rational modules restricted highest weight Frobenius twist`. Eight hits, chiefly tensor base change, Lie weight multiplication and Weyl group modules; no exact theorem.
- rg over lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json: `Steinberg|frobeniusTwist|restricted_frobenius|tensorDelta|tensorCoaction`. Hits concern semilinear Frobenius/Lang--Steinberg and unrelated Frobenius factorizations; no copy of this theorem or helper. Searching the exact item id in both source roots yielded none.
- rg `Rational|HighestWeight|Semisimple|SimplyConnected|frobenius|Coaction` in the GroupScheme project directory found the existing rational-highest-weight and Borel-pair interfaces, which were opened and reused.
- rg `tensor.*[Cc]oaction|pullbackCoaction|Coassociative|Counital` in the relevant project sources found `HopfAction.tensorCoefficients` and the comodule dictionary's tensor theorem. The dictionary is an action/coaction theorem, not an existing linear-map constructor or this simplicity result.
- rg of DAG nodes for the highest-weight terminology found `def-sfb-rational-highest-weight-data`, now cited. `tools/blueprint_refs.py search 'tensor coaction'` returned zero blueprint nodes; its ancestor command reported blueprint.from.node = None for this item. No new definition node is needed: the small composition helper belongs to the item's construction, under the human's helper authorization.
- Exact full-name searches for `tensorPullbackCoaction` and `restricted_frobenius_tensor_simplicity` in both source roots, Mathlib and the upstream name index found no declarations.

Validation: scompile.py compiles the delivered file against the published live
library, both in its sandbox module and its final library module, with no errors
or unexpected warnings. All binders and universes are explicit with autoImplicit
false. All lines are at most 100 characters. The node is JSON with indent 1,
ensure_ascii false and a final newline; lean.statement is copied verbatim from the
theorem keyword up to its assignment. Delivery dry run and push are run after
this report is written.

## Second reading by NK

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
