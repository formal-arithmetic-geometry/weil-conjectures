## Worker report

The item is stated in `lean/Sheaf/AlgebraicGeometry/FormalSystemsKernelReesFinite.lean` as
`AlgebraicGeometry.formalSystems_kernel_rees_finite`. Its proof is `by sorry`; nothing is
proved. Two supporting definition modules supply the missing homogeneous sheaf interface
and name the actual kernels and quotients. All data in these definitions is explicit.

Source read: [Stacks 087Z](https://stacks.math.columbia.edu/tag/087Z), Lemma 30.23.8, and
[Stacks 0EHN](https://stacks.math.columbia.edu/tag/0EHN), the formal-system definition and
affine description. The local literature file is absent on this machine, so the Stacks
pages were opened directly. The existing node already expands the action, zero-degree
convention and degree-zero generation implicit in the source. No correction is needed.

Hypotheses and clauses, matched individually:

- Noetherian scheme: `{X : Scheme.{ut}} [IsNoetherian X]`. The Mathlib class extends exactly
  `IsLocallyNoetherian X` and `CompactSpace X`, so it includes the node's quasi-compactness.
- Quasi-coherent ideal sheaf: `(I : X.IdealSheafData)`, through the shared `I.toModulesι`.
- Coherent formal system: `(F : CoherentFormalModule X I)`. The recorded declaration's
  object `op n` is F_(n+1); its coherent, annihilation and reduction conditions are retained.
- F_0 = 0 and K_0 = F_1: `formalKernelPiece F 0` is literally `F.obj.obj (op 0)`, and
  `formalKernelι F 0` is the identity. This is the kernel of F_1 → 0, without changing the
  existing formal-system indexing. For positive degree `n+1`, `formalKernelPiece` is the
  actual categorical kernel of F_(n+2) → F_(n+1), with its actual kernel inclusion.
- I^0 = O_X and other powers: the landed `Scheme.idealSheafPower I.toModulesι n`, whose
  zero value is the structure-sheaf module and identity inclusion. No power is redefined.
- B_n = I^n / I^(n+1): `formalAssociatedGradedPiece I n` is the shared
  `formalModuleQuotient I 1 (Scheme.idealSheafPower I.toModulesι n).1`, i.e. the cokernel
  quotient I^n / I I^n. The canonical projection is `formalAssociatedGradedπ I n`.
  I I^n = I^(n+1) as subsheaves; for n = 0, I O_X = I. Thus this gives the specified
  homogeneous quotient also in degrees zero and one.
- The sheaf direct sums: the underlying objects of the homogeneous algebra/module
  structures are the sheaf coproducts of their pieces. The actual kernel sum appears as
  `∐ (formalKernelPiece F)`. The operations are specified on homogeneous sheaves and
  extend to these sheaf coproducts, by bilinearity and sheafification. This does not identify
  sections of a sheaf coproduct on an arbitrary open with a sum of global sections.
- Associated graded algebra structure: `∃ A : GradedSheafAlgebra
  (formalAssociatedGradedPiece I)`. This structure contains bilinear multiplication into
  degree m+n, compatible with restrictions, associativity, commutativity and both unit laws.
- Homogeneous multiplication induced by local-section multiplication: the universally
  quantified clause for m, n, U, a, b produces `c` in I^(m+n)(U), whose image in O_X(U) is
  the product of the images of a and b. It then requires
  `A.mul m n U (π_m a) (π_n b) = π_(m+n) c`.
- Unit 1 mod I in degree zero: `A.unit = formalAssociatedGradedπ I 0`. The source is the
  degree-zero power O_X, so this is exactly the quotient map O_X → O_X/I, not an arbitrary
  section. The structure's unit laws evaluate this morphism at the ring section 1.
- Canonical graded module and degrees: `∃ M : GradedSheafModule A (formalKernelPiece F)`.
  Its bilinear action has source B_m(U) × K_n(U) and target K_(m+n)(U), and includes
  restriction compatibility, associativity with A's multiplication, and the unit law.
  m+n and n+m are equal; the order chosen in the file avoids dependent casts.
- Quasi-coherence of the underlying O_X-module: `(∐ (formalKernelPiece F)).IsQuasicoherent`,
  using the shared Mathlib predicate carried by `pqf-def-coherent`.
- Finite type over B with finite homogeneous generators: `M.IsLocallyGeneratedInDegreeZero`.
  It quantifies over every point p, an open neighbourhood U, a natural number t, and a
  family `s : Fin t → K_0(U)`. For every V ⊆ U, homogeneous section y ∈ K_n(V), and q ∈ V,
  a smaller neighbourhood W of q and coefficients a_i ∈ B_n(W) give
  `y|_W = ∑ i, a_i (s_i|_W)`. This is the stalkwise/local surjectivity criterion for the
  map from t unshifted copies of B to G. It proves both the general finite homogeneous
  generation clause and the more precise assertion that degree-zero generators suffice.
  It does not impose finite type over O_X.
- Specified action via lifts: for every m, n, U, a ∈ I^m(U), x ∈ K_n(U), and
  t ∈ F_(m+n+1)(U) reducing to `formalKernelι F n x`, the final implication says
  `formalKernelι F (m+n) (M.act m n U (π_m a) x) = a t`.
  This uses the actual functor transition from `op (m+n)` to `op n`. It applies on every
  open, hence on each neighbourhood where a lift exists. Such local lifts exist by the
  formal system's reduction isomorphisms, and different lifts give the same product as
  explained in the proof docstring. The formula, local surjectivity of quotient maps, and
  monicity of the kernel inclusions determine the action uniquely: the existential
  structure is canonical, rather than an unrestricted choice of action.

`HEq` in the supporting structures only handles the degree identities
(l+m)+n = l+(m+n), m+n = n+m, 0+n = n, n+0 = n. The compared section types are equal;
these fields are actual associativity, commutativity and unit equalities.
`@id Γ(X,U)` in the theorem exposes ordinary structure-sheaf ring sections for multiplication
and scalar action; it is the identity cast, with no changed section or hidden hypothesis.

Dependency declarations used, with their source signatures and docstrings read:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian` and
  `IsNoetherian` (the former is the recorded locally-Noetherian dependency).
- `Sheaf.AlgebraicGeometry.CoherentFormalModule`: `CoherentFormalModule`,
  `IsCoherentFormalModule`, `formalModuleQuotient`, `formalModuleQuotientπ`.
- `Sheaf.AlgebraicGeometry.IdealModuleProductStalk`: `Scheme.idealSheafPower`,
  `Scheme.idealModuleProduct`, `Scheme.idealModuleProductι`, used by the existing quotients.
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`: `Scheme.Modules`, its abelian category and
  colimits, and the sheaves' section objects/maps. This is the recorded sheaf-category
  dependency; no abstract category or surrogate modules are introduced.
- `Sheaf.AlgebraicGeometry.Coherent`: `RingedSpace.IsCoherent`, through the formal-system
  condition; `SheafOfModules.IsQuasicoherent` is the quasi-coherence predicate that its
  module specifies for the coherent dependency.
- The new structures use `Mathlib.AlgebraicGeometry.Scheme`'s `Scheme`, the recorded
  declaration of `def-pc-scheme`, reexported by the module-sheaf import.

Edge cases checked: the empty scheme (the pointwise generation condition is vacuous,
with the zero sheaf); zero formal system (t = 0 is allowed); zero ideal (only degree zero
survives); unit ideal (annihilation forces every formal-system term to vanish and the graded
algebra is zero); m = 0, n = 0, and both zero (identity transition and identity K_0 inclusion,
with unit acting as identity); an empty smaller open (local section generation is the
correct sheaf-local condition). No separatedness, characteristic, properness or global
finite generating family is assumed. All universes and variables are explicitly bound.

Searches made using `msearch.py T1 lem-weil-pbc-formal-systems-kernel-rees-finite`:

- LeanFinder: “sheaf associated graded algebra ideal coherent formal system kernels finite
  graded module”: localCohomology, Ideal.Filtration.submodule, homogeneous-ideal and Proj
  constructions; no exact theorem or formal-system graded sheaf components.
- Loogle: “DirectSum.GModule, SheafOfModules, GradedObject”: no hits, unknown identifier
  DirectSum.GModule. A further query “SheafOfModules, LinearMap” found generic sheaf maps,
  limits and unitHomEquiv, not a graded sheaf structure.
- LeanSearch: “graded algebra sheaf homogeneous multiplication bilinear sections graded
  module sheaf”: service unavailable, Internal Server Error. Recorded as unavailable.
- Grep: “GradedSheaf|associatedGraded|graded.*sheaf” in Mathlib/AlgebraicGeometry:
  only the unrelated Proj-as-SheafedSpace comment.
- Further LeanFinder: “graded sheaf of algebras and graded module sheaf homogeneous bilinear
  multiplication action compatible with restriction”: SetLike.gmodule, graded tensor
  products, DirectSum.gMulLHom and DirectSum.Gmodule.of_smul_of. These implement graded
  operations over a ring, not operations on sheaves compatible with restriction.
- Further LeanSearch: “successive kernel sheaves of a coherent formal module and associated
  graded ideal quotient sheaves”: service unavailable, Internal Server Error.
- Further Loogle: “CategoryTheory.Limits.kernel, SheafOfModules”: presentation relation
  kernels, not a formal-system family or sheaf associated graded pieces.
- `rg` of Mathlib, WeilConjectures and lean/Sheaf for the proposed declaration names found
  no existing names. `rg` of WeilConjectures for the item id found no statement. General
  graded-algebra search found existing ring-level `Ideal.associatedGraded` and Proj graded
  module constructions, which concern different objects and are not copied here.
- DAG searches and `tools/blueprint_refs.py search 'graded sheaf'` / `'kernel formal'` found
  no node for these interfaces. `def-nagata-sheaf-rees-algebra` describes the different
  algebra ⊕ I^n; it supplies neither this associated graded sheaf nor a generic interface.

Validation: all three modules compiled together on the server in 5.4 seconds, without
errors or unexpected warnings. The only theorem is the item's statement with `sorry`.
No dependency record is replaced and no original statement or proof is changed.

## New nodes

`def-weil-pbc-graded-sheaf-structures`: homogeneous sheaf algebra and module operations,
with all restriction, bilinearity, associativity and unit laws, plus the explicit local
finite degree-zero generation predicate. Its module is
`lean/Sheaf/AlgebraicGeometry/GradedSheafStructures.lean`. Source: the graded algebra/module
in Stacks 087Z and its affine proof. Ring-level DirectSum APIs do not supply sheaf
restriction compatibility or this sheaf-local generation predicate. Its searches are
recorded in the new node and above. Both algebra and module here are presentations by
homogeneous sheaves of the actual sheaf coproducts, not alternative module carriers.

`def-weil-pbc-formal-kernel-graded-pieces`: the actual successive kernel sheaves with their
inclusions, including K_0 = F_1, and the ideal-power quotient sheaves with their projections.
Its module is `lean/Sheaf/AlgebraicGeometry/FormalKernelGradedPieces.lean`. Source: Stacks
087Z and 0EHN. It uses the recorded formal-system and power/product/quotient declarations;
it neither introduces a second formal system nor redefines powers. The existing associated
graded-ring node only treats ideals of one ring, not sheaves, so cannot supply these objects.
The three kinds of searches are recorded in its node and above. Both new nodes are cited
by the item, with the same chapter, unit and blueprint ancestry.

## Second reading by T1

I independently opened the item, both new nodes, all three delivery modules, and the
recorded dependency declarations. I read the Stacks coherent.tex source at
section-coherent-formal (0EHN) and lemma-finite-over-rees-algebra (087Z), fetched from
https://raw.githubusercontent.com/stacks/stacks-project/master/coherent.tex because the
local literature directory is absent, and also read the rendered Stacks pages. The
section assumes a Noetherian scheme and a quasi-coherent ideal throughout. There is no
additional separatedness, properness, characteristic, field, or completeness hypothesis.

Objects, hypotheses and conclusion clauses, matched individually:

- Noetherian scheme X: `{X : Scheme.{ut}} [IsNoetherian X]`. I opened Mathlib's class,
  which extends IsLocallyNoetherian and CompactSpace, exactly the node's assumptions. Pass.
- Quasi-coherent ideal I: `(I : X.IdealSheafData)`. I opened Mathlib's structure: affine
  ideals satisfy localization compatibility. In upstream IdealSheaf.Module, toModules is
  the kernel of the structure-sheaf map to the closed subscheme and toModulesι is the
  actual kernel inclusion. This is the intended ideal, not an arbitrary module map. Pass.
- F in Coh(X,I): `(F : CoherentFormalModule X I)`. I read its full-subcategory predicate:
  coherence, annihilation by I^(n+1), and a quotient isomorphism whose composite is the
  transition. `F.obj.obj (op n)` represents F_(n+1). This agrees with 0EHN. Pass.
- F_0=0 and K_n=ker(F_(n+1)→F_n): formalKernelPiece F 0 is F_1 and formalKernelι F 0
  is the identity. At degree n+1, the definitions use kernel and kernel.ι of the actual
  transition from op(n+1) to op n. This is the required zero-degree convention. Pass.
- I^0=O_X and positive powers: the existing Scheme.idealSheafPower returns the unit module
  and identity inclusion at zero, I at one, and the image of ideal multiplication
  thereafter. I opened this recursive definition. No power notion is copied. Pass.
- B_n=I^n/I^(n+1): formalAssociatedGradedPiece is formalModuleQuotient I 1 of I^n,
  hence the cokernel of I times I^n; formalAssociatedGradedπ is its actual projection.
  I times I^n is I^(n+1), including zero by the tensor unit. Pass.
- B's associated graded algebra on the sheaf sum: `A : GradedSheafAlgebra` supplies
  bilinearity, restriction compatibility, associativity, commutativity and both unit laws.
  The theorem fixes `A.unit = formalAssociatedGradedπ I 0`. For every m,n,U,a,b the
  multiplication clause gives c in I^(m+n) with inclusion equal to the product and quotient
  equal to A.mul of the quotient representatives. This is exactly the source product.
  Existence of c on U is valid: local preimages glue since the inclusion is monic. Pass.
- G and its graded action: the actual sheaf coproduct is `∐ (formalKernelPiece F)`;
  `M : GradedSheafModule A (formalKernelPiece F)` supplies restriction-compatible
  bilinear maps B_m × K_n → K_(m+n), associativity and the unit law. Homogeneous operations
  represent those on the sheaf direct sums by bilinearity and sheafification. The encoding
  does not wrongly identify sections of a sheaf coproduct with direct sums on every open.
  The node's n+m equals the signature's m+n. Pass.
- Underlying O_X-module quasi-coherent: `(∐ (formalKernelPiece F)).IsQuasicoherent`.
  I opened the coherent dependency, which explicitly uses this Mathlib predicate. Pass.
- Finite type over B with degree-zero generators: M.IsLocallyGeneratedInDegreeZero
  quantifies over p, a neighbourhood U, t, and s : Fin t → K_0(U), then every V≤U,
  degree n, section y and q∈V. It provides q∈W≤V and coefficients in B_n(W) expressing
  y restricted to W as the sum of actions on restricted s_i. I checked every restriction
  and the quantifier order. This is local surjectivity from finitely many unshifted
  copies of B. It includes both finite homogeneous generation and the node's degree-zero
  strengthening, without imposing O_X-finite type. Pass.
- Canonical action via lifts: the final implication takes a in I^m(U), x in K_n(U), and
  t in F_(m+n+1)(U) reducing to the actual inclusion of x. It equates the inclusion of
  M.act with a acting on t. Nat.le_add_left n m gives exactly the map from level m+n+1
  to n+1. Every open is quantified, including neighbourhoods where lifts exist. Reduction
  isomorphisms give local lifts; quotient projections are locally surjective and kernel
  inclusions monic, so these formulas determine the operations uniquely. The existential
  structures therefore express canonical operations. `@id Γ(X,U)` is only an identity
  cast to ordinary ring sections. Pass.

I reviewed both new definition nodes against 087Z/0EHN and their modules. The kernel-piece
node names the actual kernels, inclusions, quotients and projections described above. The
graded-structures node states exactly the homogeneous laws and local degree-zero generation
formula implemented by its structures and predicate. HEq compares section types in degrees
that are equal by associativity, commutativity or unit identities of ℕ; no law is omitted.
Both nodes have empty proofs, null matches, three search kinds, worker/item/group creation
metadata, the item's chapter and unit, and its correct blueprint ancestor and via chain.
No dependency replacement is needed. Definitions contain no sorry data or inline missing
proof. The only theorem is the item, with by sorry; its docstring follows all four node
proof steps with their cited dependencies. Names, imports and line lengths follow the
project conventions, with no private definitions or file-local notation.

Independent searches, with phrasing different from the first reader:

- LeanFinder via msearch: "coherent adic sheaves successive kernels locally finite over
  graded ideal algebra" returned localCohomology and Ideal.Filtration.submodule, not this
  statement or a homogeneous sheaf interface.
- Loogle via msearch: "SheafOfModules, ℕ" returned zero hits.
- LeanSearch via msearch: "sheaf of graded algebras with homogeneous multiplication
  and graded module action" returned Internal Server Error. Unavailable, not a no-match.
- rg in Mathlib, upstream WeilConjectures and lean/Sheaf for associated graded, graded
  sheaf, Rees, formalKernel and proposed names found unrelated Proj and deformation
  constructions. I opened the project's gradedModuleSheaf_exists: it constructs degree-zero
  fraction sheaves on Proj, not homogeneous operations on families of sheaves on X.
  I opened Ideal.associatedGradedPiece and Ideal.associatedGraded in the project's
  AssociatedGradedRing: these are quotients over one ring and their external direct sum,
  not sheaf quotients. I searched DAG statements and opened def-nagata-sheaf-rees-algebra,
  which is the sum of unquotiented ideal powers, with no general homogeneous-sheaf
  interface. These do not supply either new notion. Proposed declaration names do not
  occur in Mathlib, upstream, or the repository's existing modules.

Edge cases: both sums retain degree zero, with identity K_0 inclusion. m=0, n=0 and both
zero give the degree-zero action and unit. Empty schemes have vacuous pointwise generation;
empty opens cause no incorrect demand for global section surjectivity. The zero system
allows t=0. For I=0 only degree zero survives; for I=O_X annihilation makes every level zero
and B is zero. No nonzero-ring, field, characteristic or nonempty-generator assumption is
introduced. The arbitrary scheme universe and shared module carrier are retained, with no
independent small test universe or unbound variables.

No mathematical mismatch was found. All Lean code and the node's statement and proof are
retained. I changed lean.statement records to the literal multiline signatures from the
files, rather than flattened whitespace, and added this independent review. All three
modules compiled together on the server in 3.9 seconds with no errors or warnings. An
initial invocation used relative paths from the wrong directory and failed before compiling;
rerunning from the sandbox compiled the intended delivery cleanly.
