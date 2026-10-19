## Worker report

The module `Sheaf.Algebra.Homology.PseudoCoherentRHomFlatBaseChange` states
`CategoryTheory.exists_pseudoCoherentRHomFlatBaseChange`, with one `sorry` and no
new definitions. It states the canonical comparison as a natural transformation,
fixes every component by the exact adjoint formula of Stacks Equation 0E1X, and
asserts that its component is invertible for pseudo-coherent E and bounded-below L.
The full seven-step node proof is in its docstring. Nothing is proved in this delivery.

I read the full node, its five original statement dependencies and their recorded
signatures/docstrings. I read Stacks more-algebra.tex, lines 28754–28852 (0E1W,
0E1X, 0A6A), and lines 28653–28711 (0ATK(3)). The source states precisely flatness,
pseudo-coherence and L in D+. There is no missing hypothesis or statement correction.
There is no repair-note file for this item in coord/repair-notes.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Commutative rings and their homomorphism R to S | `{R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)` |
| The map is flat | `(hφ : φ.Flat)` uses Mathlib's recorded `RingHom.Flat` |
| Ordinary modules regarded on the identity-only one-object site with trivial topology | `RingSiteModules R`, the existing abbreviation for module sheaves over `onePointRingSheaf R` on `Discrete PUnit` with topology bottom; `ringSiteMap φ` is the actual constant ring-sheaf map |
| The ordinary derived categories | `DerivedCategory (RingSiteModules R)` and its S analogue, using the recorded localization; `w` specifies their Hom universe |
| The derived internal Hom is the recorded one | `derivedInternalHomOfUniverses.{u, u, u, w} ⊥ (onePointRingSheaf R)` and the same over S |
| Derived extension of scalars | `(M.scalar (ringSiteMap φ)).derived`, the existing normalized universal left-derived extension, whose ordinary functor has the actual sheafified scalar-tensor object and map formulas |
| E is pseudo-coherent as an ordinary module complex | There exists a complex P representing E, `Nonempty (Q.obj P ≅ E)`, for which `DerivedCategory.IsPseudoCoherent` holds for `Q.obj` of the termwise evaluation of P at the unique object |
| L belongs to D+, explicitly by eventual cohomology vanishing | `∃ a : ℤ, ∀ i : ℤ, i < a → IsZero ((homologyFunctor (RingSiteModules R) i).obj L)` |
| Source of the canonical map | The source bifunctor of χ is `derivedInternalHomOfUniverses ... ⋙ (M.scalar ...).derived` |
| Target of the canonical map | Its target bifunctor first applies derived extension in both variables, oppositely in the first, then `derivedInternalHomOfUniverses` over S |
| Canonical adjoint construction | For every E,L, the first conjunct fixes `χ.app (op E,L)` as `adjunction.homEquiv.symm` applied to `RHom_R.map (id, unit.app L)` followed by `(α.iso ...).inv.app (op E, F.obj L)` |
| The map is an isomorphism in D(S) | The second conjunct concludes `IsIso (χ.app (op E,L))` from exactly the two object hypotheses; flatness was bound before the conclusion |
| Naturality in E and L | χ is a natural transformation on the whole product of derived categories, including arbitrary derived morphisms |
| No perfectness or Noetherian assumptions | Neither occurs in the signature; E's model may extend indefinitely to the left |

The pseudo-coherence hypothesis does not create another predicate. It applies the
recorded `DerivedCategory.IsPseudoCoherent` literally. On this site every presheaf
is a sheaf and every site morphism is an identity. Evaluation at its unique object
is therefore an exact equivalence with `ModuleCat R`, with inverse the constant
module diagram. Thus there exists such a representing P exactly when the ordinary
module derived object corresponding to E is pseudo-coherent. P itself is not required
to be a finite-free model: the recorded predicate supplies that model. There is no
chosen finite-free resolution added to the theorem's assumptions. The independent
ordinary-module localization universe is `m`, and the application explicitly sets
`A := R` and the base category of `Q`, avoiding a second inferred coefficient ring.

The parameters M, μ and α are presentations of existing canonical constructions,
not extra ring or object hypotheses. Their simultaneous existence is the landed
`scalarInternalHomAdjunction_exists`. M fixes the derived scalar extension by its
universal counit and its actual ordinary scalar-tensor formulas; μ fixes its strong
tensor comparison on actual K-flat representatives; α fixes the internal-Hom
isomorphism by evaluation, the representing Hom bijections and its uniqueness
field. Hence arbitrary equivalences or twisted scalar adjunctions are excluded.
The assertion is for every such normalized presentation. The `∀ O, HasDerivedCategory`
instance is the same ambient localization choice required by that interface;
standard localizations exist without a mathematical restriction. No equality
between the ordinary-module and ring-site derived Hom universes is imposed.

The existential χ is fully determined at every object by its first conjunct.
It is not an arbitrary isomorphism or map assumed as input. Its naturality holds
on all derived objects, and its invertibility is asserted only in the source's
specified case. This packages the canonical map and its naturality without another
helper theorem or a definition selecting undetermined existence data.

Dependency declarations used:

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`; its definition was read and
  identifies flatness with `Module.Flat R S` via φ.toAlgebra.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; their full definitions were read.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`, including its K-injective
  localization construction and representative comparisons. Publicly imported
  through ScalarInternalHomAdjunction.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and its existence statement.
  This is imported directly. M.scalar is the existing normalized presentation of
  the same universal derived scalar extension; it is not a new extension functor.
- `Sheaf.RingTheory.RingPseudoCoherent`: `DerivedCategory.IsPseudoCoherent`.
- `Sheaf.Algebra.Homology.RingHomExtensionDefs`: `RingSiteModules`, `ringSiteMap`.
- `Sheaf.Algebra.Homology.ScalarInternalHomAdjunction`: `ScalarHomModels`,
  `ScalarHomTensorComparison`, `ScalarInternalHomAdjunction` and its `iso`, and
  `SheafOfModules.ScalarDerivedPair.adjunction`/`.derived`. I read these definitions,
  their normalizations and `scalarInternalHomAdjunction_exists` in full.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules.evaluation`,
  followed by `Functor.mapHomologicalComplex`. This is termwise evaluation, so
  no derived evaluation exactness theorem is postulated as an assumption.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`.

The two additional statement dependencies are already landed:
`lem-sfb-dc-hom-scalar-adjunction` supplies the normalized internal-Hom adjunction
used by Equation 0E1X; `def-pc-ring-hom-extension-shared-definitions` supplies exactly
the existing one-object site and map. The standing §5 rule permits adding landed
nodes. The item's statement, proof and proof_deps remain verbatim. Every stated
proof dependency module is directly imported (Mathlib matches use their owning
Mathlib modules); imports needed only for the future proof are non-public.

Edge cases checked against the source and signature: either ring may be zero;
E or L may be zero; a finite-free model may have zero ranks or be unbounded to the
left; the cohomological lower bound may be any integer; no bound on positive
cohomology of L is imposed. Identity flat maps and arbitrary flat localizations
are included. No faithfulness, injectivity, finite presentation, ring regularity,
finite Tor dimension beyond flatness, or Noetherian condition is added. The
natural transformation is defined on all E,L, including those outside the
isomorphism locus; this is exactly Equation 0E1X. All universe variables and
ordinary variables are explicitly bound; automatic implicits are disabled.

Searches performed with msearch.py for NZ and this item:

- LeanFinder: `Derived Hom from a pseudo coherent complex to a bounded below complex
  commutes with flat extension of scalars` returned eight hits on Ext, derived
  functor linearity, fractions and localization; none is this statement.
- Loogle: `IsPseudoCoherent` returned zero hits (unknown identifier in Mathlib).
- Mathlib grep: `pseudo.?coherent|RHom|derivedHom` in `Algebra/Homology` returned
  25 generic bifunctor/total-complex hits; none gives the comparison theorem.
- LeanSearch: `derived Hom pseudo coherent flat base change bounded below`
  returned ordinary flatness/base-change stability, t-structure and Ext results;
  none has this conclusion.
- Direct rg in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id
  and pseudo-coherent RHom base-change variants found no existing declaration.
  `dag/lean_names_upstream.json` and project sources were also checked for the
  chosen theorem name; no clash was found.
- Direct rg in `lean/Sheaf` found existing perfect-source comparison modules and
  the general normalized scalar internal-Hom adjunction, all reused as interfaces.
  `BaseChangeRHomPerfect` assumes a perfect source and has no pseudo-coherent/D+
  statement, so cannot close this node. The occurrence in AlgebraicShriekCalculus
  is a reference to this pending lemma, not an existing statement of it.

No new node, dependency repair, statement fault or STATEMENT-DISPUTED flag is needed.

## Second reading by NZ

Author's second pass, as this dispatch explicitly forbids starting other agents;
the maintainer supplies the independent review. I reopened the node and the final
signature, checking the correspondence table above in both directions. In
particular, the comparison's direction is F(RHom_R) to RHom_S(FE,FL), α.inv is
used before scalar transposition, and the unit is applied in the covariant Hom
variable. The pseudo-coherence condition is the recorded ordinary-module notion,
not perfectness, and the lower-bound condition is cohomological. Naturality is a
natural transformation on derived categories, not just on model chain maps.

Compilation initially exposed an inferred smaller auxiliary universe in the scalar
adjunction and an ambiguity between the base category of Q and the source category
of Functor.obj. I made all scalar-comparison universe arguments explicit, set the
coefficient ring of IsPseudoCoherent explicitly to R, and placed the ModuleCat
parameter on Q itself. These repairs do not change any mathematical hypothesis.
All declared variables are bound, every line fits 100 columns, and the only proof
is `by sorry`. The final signature was copied verbatim into lean.statement.
