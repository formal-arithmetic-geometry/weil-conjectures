## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceCoherentDiagonal` states
`AlgebraicGeometry.AlgebraicSpace.coherent_diagonal`, with `sorry` only.
Source read: Stacks quot.tex, Situation 08KB (situation-coherent), Tag 08W6
(lemma-coherent-diagonal), and the inverse-pair construction of Tag 08K9.
The conclusion uses the explicitly equivalent diagonal formulation in the node.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The scheme S is `{S : Scheme.{u}}`; `universe u` is explicit, with both forms
  of autoImplicit disabled. X and B are `{X B : AlgebraicSpace S}` and the
  morphism is `(f : X ⟶ B)`.
- Finite presentation is `(hfp : ProperQuotFinitePresentation f)`, the existing
  conjunction of MapIsLocallyOfFinitePresentation, MapIsQuasiCompact of f,
  and MapIsQuasiCompact of its diagonal. No separatedness is assumed.
- The specified category C is exactly `CoherentModuli.category f`. Its object
  `base : ProperQuotTest B` retains both the S-scheme T and b:T→B. Its module
  is on `properQuotFibre f base`, the actual sheaf pullback X×_B T.
- `quasiCoherent` and `finitePresentation` are the existing Mathlib predicates
  `module.IsQuasicoherent` and `module.IsFinitePresentation`: local presentations
  by arbitrary free modules and by finite rank free modules, respectively.
- `flat` quantifies over every etale scheme chart U and uses the recorded
  scheme `Modules.IsFlatOver` on `schemeRestriction`, along the actual map U→T.
  The affine-local predicate equals stalkwise relative flatness for these
  quasi-coherent modules, exactly as stipulated by the dependency.
- `properSupport` retains Z and a representable closed immersion i, properness
  of `i ≫ properQuotSnd`, and G with IsQuasicoherent, IsFiniteType and an actual
  isomorphism `(moduleDirectImage i).obj G ≅ module`.
- `CoherentModuli.Hom.base` is a commuting map of tests over B, so it imposes
  b=b1v. `Hom.iso` is the specified tensor-pullback isomorphism. Its identity
  and composition use the existing tensor unit and composition comparisons.
- The conclusion `HasAlgebraicSpaceDiagonal (CoherentModuli.category f)` is the
  recorded criterion from def-sfb-stable-pointed-moduli-groupoids: for every
  pair of maps from S-schemes T,U, the actual moduliTwoFiberProduct is equivalent
  to discreteModuli of an algebraic space. In particular taking T=U with the
  two objects yields the Isom presheaf over T. Its naturality and full category
  equivalence are retained; no set of isomorphism classes replaces a groupoid.
  Conversely the same Isom representation after passing to T×_S U yields this
  criterion. This is precisely the node's equivalent final formulation.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: Scheme and Scheme.Hom.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicSpace, IsRepresentableWith,
  IsAlgebraicSpace, EtaleSite, Modules and structureSheaf.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers:
  fibreProduct_isAlgebraicSpace, used in the existing properQuotFibre.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: QCoh and its
  slice sheafification instances, using SheafOfModules.IsQuasicoherent.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations: moduleTensorPullback,
  moduleTensorAdjunction, moduleDirectImage, and their normalized construction.
- WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic:
  Scheme.Modules.IsFlatOver, read with its affine-local/stalkwise docstring.
- Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor: properQuotFibre, properQuotSnd,
  properQuotFibreMap and ProperQuotFinitePresentation. Read live server source
  using scompile.py --source because the node was landed recently.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties: MapIsProper,
  MapIsLocallyOfFinitePresentation, and representable closed-immersion convention.
- Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids:
  HasAlgebraicSpaceDiagonal, discreteModuli and moduliTwoFiberProduct.
- Sheaf.AlgebraicGeometry.SpaceCoherentStackGeneral: CoherentModuli, its Hom,
  identity, composition, category and projection, read locally and on the server.
  Only these definitions are used; coherent_stack_general is never applied.

Proof imports: AlgebraicSpaceFlatProperFpLocality and
SpaceModuleBaseChangeFlatProperSupport are included. The other recorded proof
notions are public through the statement imports. lem-sfb-space-module-hom-affine
has no Lean record at inspection and is therefore omitted as an unstated proof
prerequisite. It is not needed to type this stage-2 statement. The later automatic
proof import from SpaceCoherentStackGeneral back to SpaceCoherentDiagonal must
be skipped because it would close an import cycle. This is the existing contract's
explicit import-cycle exception, not a mathematical reliance on the downstream
algebraicity theorem.

Edge cases checked: b and c are allowed to differ; the two scheme maps in the
conclusion are independent, and the equalizer reduction in the proof handles
empty Isom values. Zero modules and empty schemes are allowed by all object
fields. Nontrivial automorphisms are preserved by the actual category and
its two-fibre product. The base is any algebraic space; no scheme-base,
Noetherian, separatedness, or flatness hypothesis is introduced. No universe
is equated with an independently quantified larger universe.

Searches actually run with msearch.py for this item: LeanFinder query
"The diagonal of the groupoid of flat finitely presented quasi coherent modules
with proper support on an algebraic space is representable by algebraic spaces"
returned scheme-diagonal constructions only. Loogle `"Isom", "Quasicoherent"`
returned isomorphism closure of quasi-coherence, not the result. LeanSearch
"The category of finitely presented quasi coherent modules flat over the base
with proper support on an algebraic space" returned Mathlib local presentation
predicates, not the category. Mathlib grep `CoherentModuli|coherent_diagonal|coherentDiagonal`
returned zero hits. The same rg search in lean/WeilConjectures and lean/Sheaf
found the exact category in SpaceCoherentStackGeneral. Searches of DAG definition
nodes found no independent definition node for that category; the later theorem's
supporting declarations are reused by the new existing binding. Blueprint search
`python3 tools/blueprint_refs.py search coherent` found no unit defining this
particular algebraic-space category; ancestor returned None as on the item.

Validation: scompile.py compiled the delivered module in both sandbox and library
mode cleanly. No statement correction or disputed statement.

## New nodes

`def-sfb-space-coherent-family-groupoid` binds the exact existing
`AlgebraicGeometry.AlgebraicSpace.CoherentModuli.category` and its object/arrow
types from Sheaf.AlgebraicGeometry.SpaceCoherentStackGeneral. Its self-contained
statement is Situation 08KB, without asserting the downstream algebraicity
result or adding its separatedness assumption. No Lean definition is duplicated.
The search record includes the actual LeanSearch, LeanFinder, Mathlib grep and
project grep results. Its stmt_deps are only the primitive notions it uses;
thus binding this category does not introduce a DAG edge back to the theorem
whose proof needs the present item.

## Second reading by N9

Author's second reading, not an independent review (dispatcher forbids subagents).
Reopened Situation 08KB, the item, SpaceCoherentStackGeneral and the final file.
The hfp binder matches the three required finite-presentation conditions. The
existing object fields match every module condition, with no properness of f.
The category Hom retains equality of maps to B, not merely module isomorphisms
on an arbitrarily chosen common fibre. HasAlgebraicSpaceDiagonal uses all pairs
of scheme maps and an equivalence of the actual two-fibre-product categories;
this is the node's explicit equivalent formulation. The fresh definition node
only records already existing data, and imposes no additional hypothesis.
No mismatch found. Initial exploratory code was discarded and is not delivered.
The maintainer's independent review remains the independent mathematical reading.
