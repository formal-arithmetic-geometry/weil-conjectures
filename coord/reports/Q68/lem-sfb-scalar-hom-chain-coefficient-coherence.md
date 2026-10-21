## Worker report

Module: `Sheaf.Algebra.Homology.ScalarHomChainCoefficientCoherence`.
The single postponed theorem is
`SheafOfModules.StrictScalarHom.exists_scalarHomChainCoefficientCoherence`.
All other declarations package its hypotheses/conclusions or define explicit compositions;
none chooses data from an existence theorem. No dependency node or statement is changed.

Source read: `literature/stacks-project/sites-modules.tex`, lines 815–863
(03CY, `lemma-sheafification-presheaf-modules`) and 933–961
(03CZ, `lemma-adjointness-tensor-restrict`); `sites-cohomology.tex`,
8571–8615 (0A8X, `section-hom-complexes`). The coefficient formulas beyond
these general constructions are the node's explicit agent extraction and proof.

Hypothesis and clause correspondence:

- A site small in the module universe: `C : Type c`, `Category.{v} C`, topology
  `J`, and coefficients/modules in `max c v u`. Thus site object and morphism
  universes remain independent and both lie in the module universe. The standard
  sheaf-composition, locally bijective/sheafification instances express the
  constructions on this small site, not flatness or exactness assumptions.
- Four ring sheaves and commuting arrows: `CoefficientChainSquares.square`
  quantifies `R S R' S'`, `φ a b φ'`, and `h : φ ≫ b = a ≫ φ'`.
  Square compatibility is asserted only for such squares.
- The maps supplied for every arrow and its composites: theorem input `F`
  assigns `NormalizedCoefficientMaps φ` to every coefficient arrow. Its
  `extension : Extension φ` pins the functor and maps to the existing actual
  sheafified ordinary extension. Its `chains : ScalarHomAdjunctionChains extension`
  reuses the adjunction dependency's exact nu/theta normalizations, including
  inverse theta and naturality. `alpha_evaluate` and `sigma_formula` are exactly
  the evaluation dependency's two formulas with actual product coordinates.
  The input does not require the downstream strict evaluation square, uniqueness
  proofs, coefficient equations, flatness or boundedness.
- `T_ψ`: the existing `StrictScalarHom.tensor ψ`, termwise tensor by the
  restricted unit module; `U_ψ`: existing `restriction ψ`; `H`: existing
  `CategoryTheory.homComplex`, with its actual product projections.
  Local formulas use existing `tensorSection`, `Extension.section`, `evaluate`
  and `SigmaFormula`, so tensors are sheafification-unit images and Hom evaluation
  is product projection then evaluation at the identity object of the slice.
- `χ_ψ=σ_id`: `NormalizedCoefficientMaps.homComparison` has exactly this body.
- Natural κ: `NormalizedCoefficientSquare.extensionIso`, a natural chain
  isomorphism. `extensionIso_pure` renders κ(s'⊗(s⊗x)); the added
  `extensionIso_inv_pure` renders its specified inverse on s'⊗(r'⊗x).
- Natural μ: `restrictionMate` is a natural transformation and
  `restrictionMate_pure` is μ(r'⊗z)=φ'(r')⊗z.
- Natural τ: `tensorComparison` is the displayed composition A(ν), μ, U'(κ),
  ν' inverse. `NormalizedCoefficientCompatibility.tensor_pure` supplies its
  specified local formula; `TensorNatural` and `tensor_natural` explicitly assert
  naturality in the complex. The definition contains actual maps, no choice.
- The ν equation is `NormalizedCoefficientCompatibility.nu`, in Lean's
  left-to-right composition convention. It quantifies every complex X.
- The θ equation is `.theta`: A(θ), χ_a, postcomposition with μ on the left;
  μ, restricted χ_b, restricted precomposition with κ inverse, θ' on the right.
- The α equation is `.alpha`: A(α), χ_a, postcomposition with τ on the left;
  τ_H, T'(χ_a), α' on the right.
- The σ equation is `.sigma`, quantified over arbitrary P,J,N,N',q,w,q'. Its
  premise is κ_J ≫ q' = B(q) ≫ w, exactly the node's condition. Its two paths
  use B(σ), χ_b, H(κ inverse,w) and κ_H, E'(χ_a), σ' respectively. In particular
  w need not itself be an extension of a chain map. Every induced semilinear
  target map is included by this unrestricted S'-linear map w.
- Chain maps and isomorphisms provide the signed differential equations by
  their types; `homMap` is the actual contravariant/covariant bifunctor action.
  Products range over all integers; no finite-support condition is introduced.
- The iterated-extension associators and their inverses are
  `CoefficientExtensionAssociators.comp`, `.comp_pure`, `.comp_inv`.
  Units have both specified formulas. Restriction identifications have actual
  identity-on-sections formulas in both directions. `CoefficientHomIteration`
  gives associativity and both unit laws, identity normalization of ν,χ,θ,α,σ,
  and composition equations for ν,χ,θ,α,σ. `underlyingComp` explicitly transports
  ordinary tensors through ν, restriction contraction and the extension associator.
- Identity and composite coefficient squares: `CoefficientChainPasting` has
  `kappa_id`, `mu_id`, `tau_id` and `kappa_comp`, `mu_comp`, `tau_comp`.
  All six equations use the actual normalized units/associators. The four
  coefficient equalities hold for all squares, including every pasted square;
  these comparison and Hom-iteration equations identify the successive and direct
  paths. Naturality includes further compatible target maps via the arbitrary w.
- No comparison χ is required invertible. Only κ and the ordinary extension
  associators/units are isomorphisms, as asserted by the node.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  this transparently uses Mathlib `SheafOfModules` on an arbitrary ringed site.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal` and its existing sheafified tensor.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars` (36–43), preserved by the termwise wrapper.
- `WeilConjectures.Algebra.Homology.HomComplex`:
  `CategoryTheory.homComplexFunctor`, `homComplex` (295–315), and their existing
  product-coordinate interface imported by `StrictScalarHomChain`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, `over`, `Hom.over`, `overMap`, `overFunctorMap`
  (59–88); actual slice restriction is used in the existing evaluation.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`, `homObjMap` (140–163).
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification`, `sheafificationAdjunction` (54,125), used
  by the existing tensor-section functions.
- `Sheaf.Algebra.Homology.SliceScalarHomChainAdjunction`:
  `ScalarHomAdjunctionChains`; `SliceScalarHomAdjunction.chains` supplies it.
- `Sheaf.Algebra.Homology.ScalarHomChainEvaluation`:
  `exists_scalarHomChainEvaluation`, whose alpha and sigma formulas are packaged
  here without importing a downstream existence result as a hypothesis.
- `Mathlib.LinearAlgebra.TensorProduct.Defs` / `.Basic`:
  `TensorProduct`, `TensorProduct.lift`, `TensorProduct.ext'`; the named proof
  dependency's exact Mathlib match supplies the tensor generation argument.

Existing-definition searches actually run:

1. `msearch.py ... leanfinder "Coefficient square coherence scalar extension sheaves
   Hom complexes normalized chain maps"`: eight hits, about ordinary cochain
   multiplication/scalars and presentation maps, no exact sheaf Hom coefficient theorem.
2. `msearch.py ... loogle "SheafOfModules.restrictScalars, Functor.mapIso"`:
   unknown identifier `Functor.mapIso`, zero hits; repeated with
   `"SheafOfModules.restrictScalars"`: four exact restriction-of-scalars declarations,
   reused, no coefficient-coherence theorem.
3. `msearch.py ... grep "CoefficientCompatibility|CoefficientSquare|restrictScalars"
   Algebra/Category/ModuleCat/Sheaf`: ten hits for ordinary restriction and
   pushforward; no normalized product-Hom coefficient coherence.
4. `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
   for coefficient coherence, the item id, and proposed declaration names.
   `grep -rn` for the item id in `lean/WeilConjectures`: no match. The existing
   `StrictScalarHomChain` has related coefficient structures but requires its full
   `Data`, including the downstream strict square, and omits the inverse-generator
   and identity/composition clauses. It cannot state this conditional lemma exactly.
   The new interfaces depend on only the supplied normalized maps, while reusing
   its canonical extension, tensors, evaluation and Hom action. No third tensor,
   Hom complex, restriction, sheaf Hom or module category is defined.

Edge cases checked: identity arrows; two and three successive changes; zero rings
and zero complexes; arbitrary unbounded complexes; n=0 and negative n; arbitrary
product families; nonflat coefficient maps (e.g. Z→Z/2) where χ is not invertible;
arbitrary compatible w and q', including zero maps; independent site universes.
The balance equations use only bφ=φ'a and commutative ring multiplication. Negative
Hom degrees introduce no new signs because all coefficient maps have degree zero.
Empty sites are allowed; no object or section is chosen globally.

No STATEMENT-DISPUTED issue or statement correction. The only unspecified X in the
node's first displayed coefficient equation is universally bound, as required by
its preceding phrase "natural chain maps".

## Second reading by Q68

This is the author's second reading; the dispatcher explicitly forbids starting
another agent, and the maintainer supplies independent review after delivery.
I reread the node and every displayed equation against the completed module.
The central checks were the contravariant κ inverse in θ and σ, the unrestricted
q'/w condition, and τ having an R'-linear tensor target rather than an extension
object. All match. A preliminary draft did not spell out κ inverse or the
identity/composite clauses; these are now explicit fields. I also checked that
no full `StrictScalarHom.Data` (with the downstream evaluation-square law) enters
the theorem's hypotheses: only `NormalizedCoefficientMaps` and the dependency's
`ScalarHomAdjunctionChains` do. All theorem bodies are sorry; definitions are
compositions of actual maps. No dependency repair, new DAG node, or source
statement correction was needed. Compiler and delivery results are recorded below.

Validation: scompile.py compiled the complete statement in 34.9 s (sandbox) and
30.5 s (library module); its only three warnings were line lengths, now fixed.
The initial timeout was diagnosed to untyped ring binders in the identity-unit
interfaces, repaired by explicitly binding each ring sheaf and universe.

Import-plan note: the existing parent module `StrictScalarHomChain` owns the
canonical helper constructions used by both supplied dependencies. A future
proof-only import of this delivery into that parent would close an import cycle;
that import must be omitted while the helpers remain in the parent's module.
No live source or consumer module was edited.

Final clean compile through scompile.py: sandbox 20.4 s, library module 19.0 s;
no errors and no warnings. All variables and universes are explicit, one sorry.
