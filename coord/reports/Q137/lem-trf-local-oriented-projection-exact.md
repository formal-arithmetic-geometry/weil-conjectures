## Worker report

The delivery states `CategoryTheory.GabberLocalProjection.local_oriented_projection_exact`
in `Sheaf.CategoryTheory.Sites.LocalOrientedProjectionExact`. Its proof is `sorry`.
The auxiliary definition node supplies the canonical arrows, the normalized module-lift
interface, and the actual adjunction-unit comparison. The item's mathematical statement,
proof, source, and proof dependencies are unchanged; its statement dependencies gain the
new definition node. No dependency declaration is replaced.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Strictly henselian local schemes A and S: arbitrary schemes `A S`, rings `R T`,
  `[IsStrictlyHenselianLocalRing R]`, `[IsStrictlyHenselianLocalRing T]`, and isomorphisms
  `eA : A ≅ Spec (.of R)`, `eS : S ≅ Spec (.of T)`. This spells out the definition of a
  strictly local scheme, without requiring either scheme to be definitionally a spectrum.
  The class extends the henselian local-ring class and has the separably closed residue
  field field. It imposes no Noetherian hypothesis.
- The morphism `a : A ⟶ S` is local precisely by `ha`: after these two isomorphisms,
  it sends `IsLocalRing.closedPoint R` to `IsLocalRing.closedPoint T`.
- B and `b : B ⟶ S` are arbitrary. There is no quasi-compactness, coherence, finite type,
  nonemptiness, or torsion assumption on them.
- A chosen geometric closed point is `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]` with
  `x : Spec (.of Ω) ⟶ A` and `hx` specifying its image. Its compatible image in S is
  `x ≫ a`; its geometric morphism is represented by `(point x).comp (etale a)`.
  These choices describe the geometric closed points already in the node, rather than
  adding a property of A or S. Strict locality makes different such choices equivalent.
- Small étale topoi are literally `Sheaf X.smallEtaleTopology (Type (u + 1))`.
  `etale a` and `etale b` bundle the recorded sheafified Kan-extension inverse images,
  continuous direct images, their adjunctions, and Mathlib's finite-limit preservation.
- P is `Sheaf J (Type (u + 1))`, with projections `p₁`, `p₂` and orientation `τ` satisfying
  the recorded `OrientedProduct.IsUniversal`. This is the characterization of the oriented
  product, not an extra geometric hypothesis. It permits equivalent site presentations,
  as the dependency node explicitly does, and retains the specified direction of τ.
- The canonical map Γ(S,F) → F_s is `imageGerm a x`: pull back the global section by
  the scheme adjunction unit, identify global sections of its direct image using final
  étale objects, and take the actual germ at x. The theorem supplies `d` with
  `d.hom = imageGerm a x`, so the identification is normalized, not an arbitrary isomorphism.
- `epsilon B` is the constant-sheaf/global-sections adjunction. `constantPullback b` is
  the canonical isomorphism from uniqueness of these adjunctions, using `directSections b`.
  `closedCounit a b x d` is the inverse-image mate from the constant sheaf of F_s to
  b inverse image of F: inverse of d, inverse of the constant pullback identification,
  and the actual constant-sheaf counit. `closedOrientation` takes its adjunction mate,
  in exactly the direct-image convention of `def-trf-geometric-morphism`.
- The section σ is supplied existentially, with `α` identifying its first projection
  with `x epsilon B` and `β` identifying its second projection with the identity.
  The `OrientedProduct.paste = ... closedOrientation ...` equation specifies the full
  oriented cone, not just its projections. The functor left unitor only identifies
  `Id ⋙ b_*` with `b_*`. The theorem also applies to every presentation of this canonical
  section satisfying that equation; no arbitrary section is assumed.
- Λ is an arbitrary commutative ring in the coefficient universe `u + 1`. Modules are
  exactly `ringedSiteModules.{u + 1} ((constantSheaf J RingCat.{u + 1}).obj (RingCat.of Λ))`,
  hence the category recorded by `def-weil-sheaf-of-modules-category`, not a replacement
  category of bare sets or fixed-ring presheaves. Both sites retain object universe
  `u + 1` and morphism universe `u`.
- The theorem supplies module lifts `pL` and `sL`. Each includes both functors, their
  adjunction, underlying-set natural isomorphisms, and equality of the forgotten and
  set-level adjunction hom-equivalences. `linear` specifies the scalar action using all
  generalized elements: adjoints carry `z = r x + y` to that same identity. `scale`
  sends r through the actual constant-ring sheafification unit. These conditions specify
  the induced module structures; an arbitrary pair of functors with an underlying-set
  isomorphism would not meet this definition. In particular existence of the lifts is a
  conclusion and cannot make the theorem vacuous.
- The composition isomorphism `e : sL.direct ⋙ pL.direct ≅ Id` is supplied with an explicit
  equality of its underlying map with `β`, through the two underlying-direct-image
  identifications. Thus it is the module realization of the section identity.
- The map of the node is `unitComparison ... pL sL e`: it is defined, as a natural
  transformation, by whiskering `sL.adj.unit` with `pL.direct`, associating the three
  functors, and composing with `e`. The conclusion says `IsIso` of its component for
  every module sheaf H. Naturality is built into its type and construction; it is not
  asserted only for unrelated objectwise maps.
- The final two conjuncts are `PreservesFiniteLimits pL.direct` and
  `PreservesFiniteColimits pL.direct`, i.e. exactness of this module direct image.
  Its right-adjoint left exactness is retained and its right exactness is asserted.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`,
  `Scheme.smallEtaleTopology`, including the jointly-surjective covering convention.
- `Sheaf.CategoryTheory.Sites.OrientedProductUniversal`: the recorded `universal`
  theorem, `OrientedProduct.IsUniversal`, and `OrientedProduct.paste`. The universal
  property is used rather than copying the triple category or its topology.
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`: `GeometricMorphism`, `.comp`,
  and the adjunction-mate convention. The new bundles reuse its actual structure.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, definitionally Mathlib's
  `SheafOfModules`. Underlying sets use `SheafOfModules.toSheaf` and the usual forgetful
  functor from abelian groups.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: `IsStrictlyHenselianLocalRing`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic` and `Mathlib.AlgebraicGeometry.ResidueField`:
  `IsAlgClosed` and the geometric-point convention `Scheme.SpecToEquivOfField`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`, `constantSheafAdj`.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: recorded `Scheme.etaleSetPullback`;
  its current source was read with `scompile.py --source` because the older checkout
  does not contain this landed module.
- `Mathlib.AlgebraicGeometry.Sites.EtalePoint`,
  `Mathlib.CategoryTheory.Sites.Point.Basic` and `.Skyscraper`: `pointSmallEtale`,
  `sheafFiber`, `toPresheafFiber`, its naturality, and `skyscraperSheafAdjunction`.
- Proof-only imports retain the recorded available modules for
  `strictlyHenselianOpen_toPresheafFiber_bijective`,
  `nonempty_inverseImage_representable_iso`, `smallEtaleRepresentablePresheaf_isSheaf`,
  `isConservativeFamilyOfPoints_ulift_pointSmallEtale`, Yoneda, and the concrete
  filtered-module colimit formulas. The proof-only DAG nodes
  `lem-pe-constant-left-module-inverse-image` and `lem-trf-site-point-fibre` have no
  recorded Lean module to import; the proof plan names them for stage 3. They are not
  hypotheses of this statement, and no unimplemented canonical object is chosen from them.

Source check: I read the ILO text at printed pp. 177–178, including (2.a)–(2.f),
Proposition 2.3, and Corollary 2.3.1. The source defines the section by the closed-point
counit and identifies gamma with the natural restriction on the two stalk colimits.
As the node's existing split report explains, conservativity is used on the second
factor B. The printed corollary's S/Y typo is not used to assume an extra property of B.
The theorem docstring preserves all eight proof steps, including both directions of
cofinal refinement and the identification with the specified unit map.

Edge cases checked: B may be empty (the relevant module category is zero); Λ may be the
zero ring; A and S may be separably closed points; a may be the identity; strictly local
rings need not be Noetherian. No term takes an element of B, assumes a nonzero coefficient,
or bounds any cohomological degree. A generic-point map into a nontrivial local base fails
`ha` and is correctly excluded. Universes bind all variables explicitly; no site object/hom
universe equality has been imposed. Defining the comparison through a `NatTrans` also
preserves the identity and all compatible-lift cases.

Searches for the item: LeanFinder, “Gabber exactness of the local oriented-product
projection on constant module sheaves”, returned unrelated Nöbeling and Mayer–Vietoris
exactness facts and condensed-module results. Loogle,
“GeometricMorphism, PreservesFiniteLimits, PreservesFiniteColimits”, returned no result
(the new geometric-morphism name is outside Mathlib). The Mathlib grep
“oriented.?projection|GabberLocalOrientedProjection” returned zero hits, as did the
matching source and side-library grep. LeanSearch, “Gabber exactness local oriented
product projection module sheaves”, returned localizations and generic
`SheafOfModules.instAbelian`, not the comparison. The upstream declaration-name index
also contains no declaration in the new namespace. New-definition searches are recorded
verbatim in that node's `mathlib_searches` and summarized below.

No statement correction or unresolved statement dispute is claimed. Only the theorem
proof is postponed; every definition has real data.

## New nodes

`def-trf-local-oriented-projection-arrows` records the previously absent normalized
closed-point counit, its mate, and the induced-module and unit-comparison interfaces.
Its source is ILO XI §§2.1–2.2 (2.a)–(2.f), with Stacks 00YV for algebraic structures.
It reuses the existing notions of topoi, geometric morphisms, points, stalks, constant
sheaves, and sheaves of modules. It introduces no duplicate category, no axiom, no
existence choice, and no exactness or invertibility theorem. The geometric bundles use
the existing adjunctions. The definition of `ModuleLift` characterizes the actual
constant-scalar operations and the forgotten adjunction, and the theorem supplies its
existence only in the situations required here.

LeanSearch found the existing constant-sheaf counit (reused) and unrelated locally
constant-function constructions. LeanFinder returned module pullbacks requiring an
actual functor of presented sites; those do not apply to the universal section as given.
Mathlib grep found only closed-monoidal counits named `closedCounit`. The source and
side-library search found specialized point or algebraic module lifts, not this
interface. `blueprint_refs.py search 'canonical section'` returned two unrelated units;
DAG search found this item's construction and the unstated general module inverse-image
theorem, not a separate definition of the normalized arrows. The new node therefore
records definitions needed by the item rather than moving its proof into another lemma.

## Second reading by Q137

This is the author's self-check. No independent worker was started: the dispatcher brief
forbids sub-agents and assigns independent review to the maintainer. I reopened the node
and both final modules. The correspondence above follows the binders and every conclusion
in order. I checked the directions of both mates, epsilon composition, the unitComparison
whiskering, the underlying-section normalization for e, and the actual ring-sheaf scalar
action. The helper definitions contain no `sorry`; the one theorem has exactly `by sorry`.
