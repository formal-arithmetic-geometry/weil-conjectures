## Worker report

Stage 2, Q10, `lem-sfb-flat-inertia-algebraic-space-quotient`, 2026-10-23.
The reviewed stage-1 split is preserved. Its inherited stage-1 refusal does not apply:
`coord/brief-stage2.md` §0 explicitly authorizes recording its Lean statement. There is
no repair note for this item and its live node has no Lean attachment.

The main module is `Sheaf.AlgebraicGeometry.FlatInertiaAlgebraicSpaceQuotient`, with
`AlgebraicGeometry.flat_inertia_algebraic_space_quotient`. This is the only postponed
theorem in the delivery; its proof is `sorry`, and its docstring contains all eight
steps of the accepted split and their dependency names. The two definition modules
contain real data and no postponed theorem. Category laws are proved as structure
fields, not as additional mathematical lemmas.

Hypothesis and conclusion audit:

| Node clause | Lean rendering |
| --- | --- |
| A scheme S in the prescribed universes | `{S : Scheme.{u}}`; independent `universe u v w` and `BasedCategory.{v,w} (Over S)` retain the total category's object and morphism sizes. The site, its sets, charts and algebraic spaces use exactly the existing dependency's universe u. |
| An algebraic stack over S | `F` and `hF : IsAlgebraicModuliStack F`, using the recorded definition without specialization to DM stacks. |
| Inertia objects (x,a), with a an automorphism | `ModuliInertiaObject F` stores `obj`, the actual `obj ≅ obj`, and `vertical : F.p.map automorphism.hom = 𝟙 _`. |
| Inertia projection sends (x,a) to x | `moduliInertiaProjection F`; its functor maps objects to `.obj` and arrows to the underlying arrow. |
| Projection representable by spaces, flat and locally of finite presentation after scheme base change on étale charts | `hI : HasFlatLocallyPresentedModuliInertia F`; this quantifies over every scheme T and scheme-to-F map, uses the existing `HasSpaceBaseChange` with its specified projection p, and requires `Flat ((yoneda.preimage (a ≫ p)).left)` and `LocallyOfFinitePresentation ...` on every `AlgebraicSpace.IsEtale a` chart. |
| P(T) is Ob(F(T))/isomorphism, compatibly with restriction | `Q.toModuliIsoClassPresheaf`; `classMap` is a functor over the base, and `class_bijective` requires its actual fibre functor to induce a bijection on Mathlib skeletons for every T. The fibre of `discreteModuli P` is the discrete set P(T), by Yoneda. This identifies precisely the quotient, with no arbitrary point-set map or replacement groupoid. |
| Q is the fppf sheafification of P | `Q.sheaf`, `Q.unit`, and `Q.universal`; the last is bijectivity of composition with the unit into EVERY fppf sheaf. These are the full existing sheafification universal property, not algebraicity or any conclusion of this theorem. |
| The natural map π | `Q.projection` is definitionally `Q.classMap.comp (discreteModuliMap Q.unit)`. |
| Q is an algebraic space | First conjunct `AlgebraicSpace.IsAlgebraicSpace Q.sheaf`, the recorded algebraic-space predicate. |
| π is smooth and surjective, without being required representable | The second conjunct gives a genuine smooth surjective scheme atlas `a : h_U → F` and `b : h_U → Q`, with a vertical `ModuliTwoIso (a.comp Q.projection) (discreteModuliMap b)`. Every scheme base change of b is smooth and surjective by `AlgebraicSpace.IsRepresentableWith (fun _ _ p ↦ Smooth p.left ∧ Surjective p.left) b`. This is exactly the smooth atlas test for π. Surjectivity of b and of the atlas implies surjectivity of π. No representability predicate is imposed on π. |
| If F→S is smooth, Q→S is smooth | Third conjunct: `IsSmoothModuliStack F → ∀ V b, AlgebraicSpace.IsEtale b → Smooth V.hom`. This is the target étale-chart definition of smoothness of Q over S. |

The parameter `Q : ModuliIsoClassSheaf F` packages the node's “let Q be the
sheafification”. Its data are determined up to unique compatible isomorphism; this
is not an extra geometric hypothesis or a choice of an arbitrary map. The structure
avoids assuming sheafification for every presheaf on a large site merely to speak
about this one presheaf. For direct use with the recorded Mathlib API,
`ModuliIsoClassPresheaf.sheafification` constructs this package from the ACTUAL
`presheafToSheaf` value and `toSheafify` unit. Its universal field is the bijectivity
of `sheafificationAdjunction.homEquiv`. No existence theorem with a sorry proof is
used to choose any object, map, category, or structure.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack`, `IsSmoothModuliAtlas`,
  `IsSmoothModuliStack`, and its chart conventions.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids` (imported publicly by the
  definitions above): `BasedCategory`/`BasedFunctor` from Mathlib, `discreteModuli`,
  `discreteModuliMap`, `moduliFiberMap`, `ModuliTwoIso`, `HasSpaceBaseChange`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace`, `.IsEtale`, `.IsRepresentableWith`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat` (read full
  affine-local definition and stalkwise identification).
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` (full affine-local signature).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth` (full
  affine-local definition). The current name Smooth is used, avoiding IsSmooth's
  deprecated alias.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfTopology`, with the slice
  `Scheme.fppfTopology.over S` supplied by the existing stack/space modules.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`, `toSheafify`,
  `sheafificationAdjunction`; the new constructor uses all three directly.
- `def-weil-size-convention` is the recorded metatheoretic convention, with no
  declaration: universes are explicit and no equality is imposed on u, v or w.

Recorded proof dependency modules are imported with plain `import`:
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`,
`WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`. Other mathematical
proof dependencies currently have no Lean attachment and hence supply no import;
their names remain in the proof docstring. This delivery does not formalize those
proofs or reopen the accepted split.

Sources checked locally: `stacks-morphisms.tex`, 06QJ and 06QD (including their
proofs), 0DN8; `categories.tex`, 034H, 034I and 042H; `spaces-descent.tex`, 0AHD.
The current blueprint `literature/blueprint/latest` resolves to main-20261023-1620;
its direct-images statement and proof were read. This generic auxiliary quotient
statement is not itself a blueprint unit statement. The existing null ancestor and
its explicit Picard/alteration place are retained in the new nodes' ancestry.

Edge cases checked before writing and again against the final signatures:

- Empty stack: the class sheaf and atlas can both be empty; all scheme/chart tests
  and the base-smoothness implication still make sense. No Nonempty or point is
  required.
- A stack already represented by a space: its class presheaf is that space, its
  sheafification is itself up to the unique unit-compatible isomorphism, and π is
  the identity under this identification.
- Nonreduced test schemes are retained: both inertia base changes and the class
  bijection quantify over EVERY `Over S`, not only field-valued points.
- In characteristic p, `Bμ_p`: inertia is flat lfp but not smooth. Only its actual
  flatness and lfp are required; π to Spec k is allowed to be nonrepresentable.
  Smoothness of π is tested by the smooth stack atlas, not by an assertion that
  μ_p or the stabilizer quotient R→R/G is smooth.
- Nontrivial automorphisms are retained in inertia and the original stack; only
  the specified skeleton quotient forgets them. A coarse space merely bijective
  on geometric points would not satisfy the required class-presheaf condition.
- Arbitrary choices of a presentation of the class presheaf or sheafification are
  allowed only with their full quotient/universal properties; the resulting map
  is canonical up to the appropriate unique identification.
- The structural smoothness conclusion covers arbitrary étale scheme charts,
  including the empty chart; it is not restricted to one arbitrarily chosen V.

Searches performed through the prescribed `msearch.py` (exact query and returned
hit names are retained in each new node's `mathlib_searches`): LeanFinder for the
flat-inertia quotient theorem (8 unrelated scheme-smoothness results); Loogle
`"Inertia", "Sheaf"` (0); Mathlib grep `[Ii]nertia|[Aa]lgebraic[Ss]tack` restricted
to AlgebraicGeometry (0). LeanSearch for sheafification of stack classes (8 generic
sheafification results), and for inertia objects/arrows (8 automorphism-group
results). LeanFinder for the isomorphism-class presheaf (8 Grothendieck/fibre
category results), and for inertia flat lfp (8 scheme flatness results).
The exact general-class-presheaf LeanSearch returned only ordinary sheafification.
The targeted Mathlib grep for `ModuliIsoClass|ModuliInertia|IsoClassPresheaf|InertiaStack`
returned 0. Direct `rg` searches of both `lean/WeilConjectures` and `lean/Sheaf`
found no general inertia/class-presheaf declaration or this theorem; the item-id
search of upstream found none. Related modules DMGeometricInertiaTrivial and
StablePointedModuliGroupoids were opened and reused, not copied.
DAG definition searches and `tools/blueprint_refs.py search` for “isomorphism
classes” and “inertia” found only specific Picard/torsor, ramification, or smallness
notions, not the two generic definitions needed here.

No statement correction, dependency-record repair, or statement dispute is needed.
Only the item's `lean` record and the addition of two new definition IDs to its
`stmt_deps` change. No live repository file was edited and no direct git command
or local/global build was run.

Validation: `scompile.py Q10 lem-sfb-flat-inertia-algebraic-space-quotient` with
all three modules, each compiled separately in dependency order, passed with no
errors or unexpected warnings (about 3.0–3.3 seconds per file). The first dry
run requested the mandatory empty `import_flags` arrays on the new definition
nodes; these were supplied before rerunning preflight.

## New nodes

`def-sfb-moduli-inertia` supplies the genuine category of vertical automorphisms,
its forgetful projection, and the scheme-base-change/étale-chart predicate for
flat locally finitely presented inertia. Its module is
`Sheaf.AlgebraicGeometry.ModuliInertia`; all category data and operations are
explicit. Source: Stacks 034H, 034I, 042H and 06QJ. The searches above find
individual automorphism groups and scheme flatness, but no inertia category.
The existing stack definitions provide all base-change and algebraic-space data;
there is no second definition of an algebraic stack or algebraic space.

`def-sfb-moduli-isomorphism-class-sheaf` supplies the exact fibrewise
isomorphism-class-presheaf interface and the fppf sheafification with its unit and
full universal property. Its module is
`Sheaf.AlgebraicGeometry.ModuliIsoClassSheaf`. Source: the displayed presheaf in
Stacks 06QD and the existing sheafification universal property. Skeletons, fibre
functors, the discrete fibred-category construction and Mathlib's sheafification
adjunction are reused. None of the search results supplies this general stack
class-presheaf notion. The constructor using `presheafToSheaf` and `toSheafify`
is included, so the universal presentation does not introduce a competing
sheafification functor. Both new nodes are direct statement dependencies of the
item, and their source and statement are self-contained.

## Second reading by Q10

A separate final pass opened the final node and all three final Lean modules;
this is a self-review, with the independent delivery review left to the maintainer
as instructed by the dispatched brief. No other agent was started.

The pass rechecked each table row above, in particular that inertia automorphisms
are vertical, that commuting-arrow order is α≫f = f≫β, and that the projection
on a scheme base change is the projection required by `HasSpaceBaseChange`.
It checked that `class_bijective` is on actual fibre functors and that the unit
universal property is factorization into all sheaves. It checked the canonical
formula for `Q.projection` and the `ModuliTwoIso` identifying the atlas composite
with b. Smoothness and surjectivity are asserted for b on every scheme base
change, while π itself is never required representable. Finally the implication
uses `IsSmoothModuliStack F` and tests the structural map of every étale scheme
chart of the same Q, not a new unrelated space. These are exactly all the
hypotheses and clauses of the unchanged statement. No mismatch was found.
The constructor from the recorded Mathlib sheafification adjunction was added
to make compatibility explicit and was included in the clean server compile.
