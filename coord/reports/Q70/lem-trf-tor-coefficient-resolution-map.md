## Worker report

The module `Sheaf.RingTheory.TorCoefficientResolutionMap` states
`ModuleCat.tor_coefficient_resolution_map`, with the canonical chain map, the
resolution-computation isomorphisms, the two uniquely specified tensor extensions,
their commuting square, and both values on arbitrary finite cycle sums. There is no
statement correction, dependency repair or new node. Only the item's `lean` changes.
All theorem proofs are `sorry`; all helper definitions contain actual constructions.

Hypotheses, one by one:

- Commutative rings R, A and B are the three `Type u` binders and `CommRing` instances.
  The maps R → A → B are `Algebra R A`, `Algebra A B`; `Algebra R B` and
  `IsScalarTower R A B` specify the composite. Thus the node's g is `algebraMap A B`.
  This is the same size convention as the recorded Tor coefficient dependencies;
  any three rings and module may be placed in a common universe.
- `M : ModuleCat.{u} R` is the arbitrary R-module, including the zero module.
- `P : ProjectiveResolution M`, together with
  `[∀ j : ℕ, Module.Free R (P.complex.X j)]`, is exactly an augmented exact free
  resolution. ProjectiveResolution stores exactness and the augmentation; termwise
  projectivity follows from freeness, so it adds no mathematical restriction.
  P is supplied, never replaced by a chosen projective-resolution model.
- `n : ℕ` is every nonnegative homological degree. The complex shape is `.down ℕ`:
  it encodes extension by zero below zero, including the zero outgoing differential
  in degree zero. Tensoring uses only `P.complex`, without its augmentation.
- There is no flatness, faithful flatness, nonzero-ring, finite-rank, or finite-length
  hypothesis, and no bijectivity assertion for either tensor extension.

Clauses and constructions:

1. `torResolutionCoefficientComplex R S M P` is an abbreviation for Mathlib's
   `(tensorRight (ModuleCat.of R S)).mapHomologicalComplex (.down ℕ)` applied to
   P.complex. This is the node's C for S=A and D for S=B. It is an interface to the
   existing tensor-complex construction, not a replacement definition of tensor or
   homology.
2. `torResolutionCoefficientChain` is literally `NatTrans.mapHomologicalComplex`
   applied to the existing tensoring-right transformation for the underlying
   R-linear coefficient homomorphism `IsScalarTower.toAlgHom R A B`. Its type is a
   morphism of complexes, so it includes the chain identity. The theorem's first
   conjunct states its component formula p tensor a ↦ p tensor g(a). Its second
   conjunct states A-linearity using the R-linear coefficient-multiplication
   endomorphisms: phi((1 tensor mul_a)x) = (1 tensor mul_g(a))(phi(x)). This expresses
   the A-action on the second tensor factor and restriction along g, without
   installing a competing action on Mathlib's R-module tensor objects.
3. `torResolutionCoefficientAddEquiv` is the recorded canonical
   `P.isoLeftDerivedObj (tensorRight (ModuleCat.of R S)) n`, forgetting only its
   R-linearity to use Mathlib's action-transport API. Its underlying function is
   exactly iota, not a selected unspecified isomorphism.
4. `torResolutionHomologyModule` retains the actual Mathlib homology group and its
   additive structure, transporting the existing coefficient module structure
   through that canonical isomorphism with `AddEquiv.module`.
   `torResolutionCoefficientIso` is the same iota made S-linear using
   `AddEquiv.linearEquiv`. The companion theorem
   `torResolutionHomologyModule_smul` identifies the transported action, on every
   homology class, with the homology map of 1 tensor multiplication by s. Thus the
   homology action is exactly the multiplication action specified by the node.
   This applies with S=A and S=B. The coefficient action restriction and tower
   formula are already supplied by `tor_resolution_coefficient_actions`.
5. The node writes T tensor_A B. The theorem uses B tensor_A T, identified by the
   canonical tensor symmetry t tensor b ↔ b tensor t. Both maps in `maps` are
   B-linear, with their usual B-action on the first factor. `maps.1` is c_n and
   `maps.2` is alpha_n. The first two clauses inside `∃! maps` state, for every b,t,x,
   c_n(b tensor t) = b Tor(M,g)(t) and
   alpha_n(b tensor x) = b H_n(phi)(x). These formulas characterize the maps on
   generators; unique existence asserts the well-defined balanced extensions,
   not merely the existence of arbitrary maps with an unrelated square.
6. `HomologicalComplex.homologyMap (torResolutionCoefficientChain ...) n` is the
   exact h_n in the node. `torCoefficientLinearMap ... (Algebra.ofId A B)` is the
   recorded coefficient map induced by g. The `@id` annotations select the
   coefficient-B action or homology-B action on their unchanged underlying groups.
7. The third clause inside unique existence is equality of B-linear maps:
   `iota_B.toLinearMap.comp maps.1 = maps.2.comp (LinearMap.baseChange B iota_A)`.
   `LinearMap.baseChange B` is precisely 1_B tensor iota_A. After tensor symmetry
   this is the displayed iota_B c_n = alpha_n (iota_A tensor 1_B).
8. The last clause quantifies every finite length k, p : Fin k → P_n,
   a : Fin k → A, and z in C.cycles n whose inclusion is the tensor sum.
   For every b it supplies w in D.cycles n whose inclusion is exactly
   sum p_i tensor (g(a_i)*b). It then states that both iota_B applied to
   c_n(b tensor iota_A^{-1}([z])) and alpha_n(b tensor [z]) equal the actual
   class `[w]`, using Mathlib's `homologyπ`. Every finite sum has a Fin k indexing,
   so no support-size restriction is imposed. The square and iota inverse identity
   identify the latter with the node's second composite on the very same input.

Dependency declarations used (full signatures and docstrings read):

- `Mathlib.LinearAlgebra.FreeModule.Basic`: `Module.Free`, including its empty-basis
  case and `Module.free_iff_set`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`, `.Basic`, `.Map`, `.Tower`:
  `TensorProduct`, `TensorProduct.mk`, `TensorProduct.lift`, `TensorProduct.ext'`,
  `LinearMap.rTensor`, `TensorProduct.map`, `LinearMap.baseChange`. These are the
  module-tensor-product dependency and the canonical extension-of-scalars map.
- `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`:
  `HomologicalComplex.homology`, `.cycles`, `.iCycles`, `.homologyπ`, `.homologyMap`.
- `Mathlib.CategoryTheory.Monoidal.Tor`: `CategoryTheory.Tor'`.
  The canonical computation is `ProjectiveResolution.isoLeftDerivedObj` from
  `Mathlib.CategoryTheory.Abelian.LeftDerived`.
- `Sheaf.RingTheory.TorCoefficientModule`: `ModuleCat.torCoefficientModule`,
  `ModuleCat.torCoefficientLinearMap`; the definitions use the actual Tor functor,
  its multiplication endomorphisms, and the underlying R-linear coefficient map.
- `Sheaf.RingTheory.TorResolutionCoefficientActions`:
  `ModuleCat.tor_resolution_coefficient_smul` and
  `ModuleCat.tor_resolution_coefficient_actions`. The former identifies the
  transported homology action, the latter supplies action restriction and balancing.
- Proof dependencies are available through those imports:
  `Module.Projective.of_free` (`Mathlib.Algebra.Module.Projective`) and
  `ProjectiveResolution.leftDerived_app_eq` (`Mathlib.CategoryTheory.Abelian.LeftDerived`),
  clause (2) of the recorded Tor-map-via-resolution-lift leaf. The first-variable
  naturality clause `isoLeftDerivedObj_hom_naturality` was also read.
- `Mathlib.Algebra.Module.TransferInstance`: `AddEquiv.module`,
  `AddEquiv.linearEquiv`; these transfer the action without changing the additive
  group and introduce no unspecified data.

The Stacks source was read in `literature/stacks-project/algebra.tex`: section Tor,
Lemma tor-welldefined and the following second-variable functoriality paragraph
(Tags 00LY/00LZ), section Functorialities for Tor item (1) (00M7), and the flat
base-change lemma (00M8). Only the map-identification argument is used, as the
node requires; none of 00M8's flatness or isomorphism conclusion is imported.

Searches actually run with msearch.py for this item:

- leanfinder: "Canonical Tor coefficient base change map commutes with the computation
  on any free resolution and sends cycle tensors by the coefficient ring homomorphism".
  Eight hits on IsBaseChange, tensor universal properties and tensor towers, including
  `TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange` and
  `LinearMap.liftBaseChange_tmul`; no complete statement match.
- loogle: "CategoryTheory.ProjectiveResolution.leftDerived_app_eq, TensorProduct.lift".
  Service succeeded with zero hits for the combined query.
- grep: "torCoefficient|coefficient.*resolution|resolution.*coefficient" in CategoryTheory.
  Service succeeded with zero hits.
- leansearch: "Tor coefficient change canonical map computed by tensoring an arbitrary
  free resolution and multiplying the coefficient". Eight hits, including
  `CategoryTheory.Tor`, `CategoryTheory.Tor'_map_app`, `LinearMap.tensorProduct`,
  `TensorProduct.AlgebraTensorModule.map_eq`; none states the full square and cycle formula.
- Local rg in both `lean/WeilConjectures` and `lean/Sheaf` for torCoefficient,
  tor_resolution, and coefficient/resolution combinations found the two recorded
  dependencies, `TorFlatBaseChange`, `TorCoefficientLocalization`, the degree-one
  `TorOneSurjectiveFlatMiddle`, and the private Tor-symmetry naturality lemma.
  The latter is general R-linear naturality, not this B-linear extension square.
  `grep -rn` for this item's id in `lean/WeilConjectures` found no match.
  The proposed exported names were also searched in Mathlib and both project roots,
  with no collisions.

The already landed downstream `TorFlatBaseChange` defines a canonical coefficient
extension with the same pure-tensor formula, but no resolution-comparison square.
This delivery does not define a second c_n: it characterizes the unique pair of
extensions in its theorem. It imports neither that downstream theorem nor its
module, preventing a dependency/import cycle when that proof uses this result.
Its c_n is identified with the map supplied here by the defining formula and
uniqueness, under tensor symmetry and the existing action restriction equality.

Edge cases checked mathematically before writing and again against the signature:

- n=0 uses the unaugmented complex, so H_0 is a cokernel rather than the augmented
  complex's zero homology. No positive-degree-only comparison occurs.
- k=0 gives zero cycle sums; the class and both tensor values are zero. k is not
  required positive, and arbitrary finite supports are covered by Fin k.
- M=0, zero resolution terms, zero coefficient rings and the zero ring R are
  permitted; there is no Nontrivial instance or nonempty-basis requirement.
- g=id gives the identity coefficient chain map and multiplication extension;
  the square is the coefficient-linearity identity.
- For R=A=Z, B=Z/2, M=Z/2 and n=1, Tor(M,A)=0 whereas Tor(M,B)=Z/2.
  The extension is not asserted invertible, and its source and image are zero.
  This is an explicit nonflat test of the absence of any isomorphism claim.
- P is arbitrary throughout, so no basis choice, resolution finiteness or chosen
  comparison lift removes any resolution covered by the node.

Validation: scompile.py compiled the sandbox module and its final library module
without errors or warnings other than the permitted sorry diagnostics. The final
file has explicit universes and `set_option autoImplicit false`, no local notation
or file-local instance, no lines over 100 characters, and no `let` in a statement.
No STATEMENT-DISPUTED flag or node fault remains.

## Second reading by Q70

No second agent was started: the dispatcher explicitly forbids it. The maintainer's
independent review reads the delivery. A final in-thread reread checked each binder,
the coefficient-factor action, the canonical underlying iota, the g-induced h_n,
the B-linear types and pure-tensor characterizations, tensor symmetry, the actual
map equality, and both finite-cycle values against the unchanged node. The
elaboration pass found that action transport needed an explicitly typed additive
isomorphism with target `torCoefficientModule`; that helper was added so the
transport uses the coefficient S-action rather than the original R-module action.
The final file compiled cleanly after this correction. No mathematical clause or
node field outside lean was changed.
