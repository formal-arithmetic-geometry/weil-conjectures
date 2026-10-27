## Worker report

The delivery states `AlgebraicGeometry.galois_clopen_component_cover` in
`Sheaf.AlgebraicGeometry.GaloisClopenComponentCover`. Its sole proof is `by sorry`.
There are no definitions, extra nodes, dependency repairs or statement corrections.
The existing node changes only in `lean`.

Sources read: ILO, Travaux de Gabber, Expose X, 2.3 Step 2, printed p.150
(PDF page index 155): the Galois group permutes components transitively and H is
one component's decomposition subgroup. Also read the current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`sk-thm-sf-ctf-stability-direct-images.md`, and Stacks `pione.tex`, section
`section-finite-etale-under-galois` (Tag 03SF), including the geometric-fibre
transitivity and simple-transitivity characterizations. The node extracts the
already-given Galois scalar-extension part of the source argument; its six-step
proof is reproduced in the theorem docstring.

Hypotheses, clause by clause:

- The field e is `(e : Type u) [Field e]`; e0 is L with `[Field L] [Algebra e L]`.
  Its finite degree is `[Module.Finite e L]`, separability is
  `[Algebra.IsSeparable e L]`, and normality is `[Normal e L]`. Mathlib's normality
  says the minimal polynomial of each element splits; for a field extension
  this is the node's equivalent irreducible-polynomial-with-a-root definition.
- B is `(B : Scheme.{u}) [IsIntegral B]`, with the e-structure morphism b.
  `IsIntegral` itself includes nonemptiness and implies irreducibility/reducedness.
- `Y`, `p`, `q`, and `hY : IsPullback p q b (Spec.map ... (algebraMap e L))`
  present precisely B times Spec L over Spec e. This is a presentation of the
  fibre product, not an arbitrary cover: hY asserts its full universal property.
  Choosing the standard `pullback` and its projections gives this presentation;
  conversely the canonical pullback isomorphism transports every clause.
- The finite indexing family is `(I : Type v) [Finite I] (U : I → Y.Opens)`.
  `hcomp` says each underlying subset is an irreducible component; components
  are nonempty by the definition of `IsIrreducible`. `hclosed` supplies closedness;
  openness and the induced open scheme structure are already in `Y.Opens` and
  `(U i).toScheme`. `hdisjoint` is pairwise disjointness, and `hcover : iSup U = ⊤`
  is the cover of Y. Thus all components occur; a missed nonempty component
  would meet one of these components and contradict the clopen decomposition.

Conclusions, clause by clause:

- `∃ a : (L ≃ₐ[e] L) →* Aut Y` supplies the canonical left action. Its two
  equations say `(a g).hom ≫ p = p` and its q-projection is q followed by
  `Spec.map g.symm.toRingHom`. These uniquely characterize id_B times Spec(g^-1)
  by hY. This is not a choice of an unspecified action or a hypothesis assuming
  such an action. The monoid hom asserts identity and multiplication laws.
  Mathlib's `Aut_mul_def` composes in the ordinary function-action order.
- For every `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]` and
  `(t : Spec (.of Ω) ⟶ B)`, the finite nonempty J and the isomorphism
  `Over.mk (pullback.snd p t) ≅ Over.mk (Sigma.desc fun _ : J ↦ 𝟙 (Spec (.of Ω)))`
  say the geometric fibre is a nonempty finite disjoint union of copies of
  Spec Ω *over Spec Ω*. An isomorphism of bare schemes would not suffice.
- `∃ x, x ≫ p = t` makes nonemptiness of geometric lifts explicit. For every
  two such lifts x,y, `∃! g, x ≫ (a g).hom = y` is simple transitivity, including
  freeness and transitivity. The maps are actual scheme morphisms from Spec Ω;
  the residue embeddings are retained, not reduced to points of Y.
- `∀ i j, ∃ g, (a g).hom '' (U i : Set Y) = (U j : Set Y)` is transitivity
  on the given components. Together with the cover, this is all components.
- For each i, the subgroup H is characterized by
  `g ∈ H ↔ (a g).hom '' (U i : Set Y) = (U i : Set Y)`, so it is exactly H_i.
  `r : H →* Aut (U i).toScheme` is its restricted action, characterized by
  `(r h).hom ≫ (U i).ι = (U i).ι ≫ (a h.val).hom`. The open inclusion is mono,
  so this fixes r, rather than giving an arbitrary action.
- `IsFinite ((U i).ι ≫ p) ∧ Etale ((U i).ι ≫ p) ∧ Surjective ((U i).ι ≫ p)`
  states the three properties of u_i.
- For each Ω,t the final existential lift gives a nonempty component geometric
  fibre. For every two lifts over t, `∃ h : H, x ≫ (r h).hom = y` says it is a
  single H_i-orbit. This is precisely the node's equivalent formulation.
  The projection/action equations also ensure all the restricted actions are
  over B, hence preserve these fibres.

Dependency interfaces read and used (directly or through their stated standard
notions; no copies introduced):

- `def-weil-field`: Mathlib.Algebra.Field.Defs, `Field`.
- `def-pc-field-extension`: Mathlib.Algebra.Algebra.Defs, `Algebra`, `algebraMap`.
- `def-pc-field-tower`: Sheaf.FieldTheory.FieldTower, `FieldExtension.degree`;
  its module docstring explicitly records `Module.Finite` for the finite clause
  used here (the degree itself is not needed in the signature).
- `def-pc-integral-scheme`: Mathlib.AlgebraicGeometry.Properties,
  `AlgebraicGeometry.IsIntegral`.
- `def-pc-fibre-product` and `def-weil-geometric-fibre`:
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback,
  `pullback`, `pullback.snd`; the displayed scalar-extension square uses
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs, `IsPullback`,
  which is exactly the same universal property with named projections.
- `def-weil-irreducible-components`: Mathlib.Topology.Irreducible,
  `irreducibleComponents`, `IsIrreducible`.
- `def-weil-algebraic-closure`: Mathlib.FieldTheory.IsAlgClosed.Basic,
  `IsAlgClosed`, imported through the recorded AlgebraicClosure module.
  Ω need only be algebraically closed, not an algebraic closure of e.
- `def-weil-finite-integral-morphism`: Mathlib.AlgebraicGeometry.Morphisms.Finite,
  `AlgebraicGeometry.IsFinite` (the integral-map clause is not used).
- `def-weil-etale-morphism`: Mathlib.AlgebraicGeometry.Morphisms.Etale,
  `AlgebraicGeometry.Etale`.
- `def-weil-surjective-morphism`: Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap,
  `AlgebraicGeometry.Surjective`, exposed by the finite/etale imports.
- `def-weil-pbc-separable-algebraic-extension`: Mathlib.FieldTheory.Separable,
  `Algebra.IsSeparable`.
- Normality uses Mathlib.FieldTheory.Normal.Defs, `Normal`, the existing class;
  the same module supplies `Normal.algHomEquivAut`, matched by proof dependency
  `lem-sfb-normal-embeddings-automorphism-transitive`.

Stated proof-dependency modules are included as plain imports:
`WeilConjectures.Mathlib.RingTheory.Etale.Field` for
`Algebra.Etale.of_finite_of_isSeparable`,
`WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree` for
`Scheme.Hom.exists_overIso_sigma_of_isSepClosed`, and
`Mathlib.AlgebraicGeometry.PullbackCarrier` for surjective base change.
The other Mathlib proof interfaces (Spec, finite and etale base change, field
normality and irreducible components) are already among public statement imports.
`lem-sfb-finite-etale-clopen-restriction` has no Lean/module record in the read
repository, so no import can be added for it yet; it is a proof dependency only,
not a missing notion needed to state this theorem. Its future proof import
can be added when its module is published.

Edge cases checked before writing and during the second pass:

- L=e: the action group is trivial, Y is B, and the component fibre is one copy
  of Spec Ω. No nontrivial-extension hypothesis occurs.
- A split extension over B can give several components with trivial stabilizer;
  each such component fibre is a single lift, compatible with the assertion.
- Empty B is excluded exactly by the node's integrality/nonemptiness assumption.
  An empty component is excluded by `hcomp`; an empty I cannot cover this Y,
  which is nonempty by faithful field base change of nonempty B. No extra
  Nonempty I assumption is imposed.
- Arbitrary characteristics, nonnormal integral B, and integral B without
  Noetherian, proper, or finite-type assumptions are retained.
- Universes u,v are explicit and `autoImplicit` is false. Component index I has
  an independent universe v; Ω and all scheme/ring data use the ordinary
  Scheme.{u} size convention, as the recorded geometric-fibre API does. Since u
  is arbitrary, larger fields are handled by placing the entire diagram in a
  common larger universe; there is no smaller independent universe of test
  fields causing vacuity.

Searches made with the authorized `msearch.py Q27 <item>` wrapper:

- LeanFinder: "Finite Galois scalar extension of an integral scheme has transitive
  clopen components and component stabilizers act transitively on geometric
  fibres". Eight hits, including abstract Galois-category transitivity,
  `Ideal.isPretransitive_of_isGalois`, and `IsGaloisGroup.iff_isFractionRing`.
  None states this scheme-theoretic conjunction or the specified scalar action.
- Loogle: `"AlgebraicGeometry", "Galois"`. Zero hits.
- Mathlib grep: `Galois.*([Cc]omponent|[Ff]ib[er]+)|([Cc]omponent|[Ff]ib[er]+).*Galois`
  in AlgebraicGeometry. Zero hits.
- LeanSearch: "The geometric fibre of Galois scalar extension is a torsor, and
  stabilizers of clopen irreducible components act transitively on component
  fibres". Eight hits, including the same prime-ideal transitivity and abstract
  Galois-category orbit results; no exact match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for Galois/component
  combinations, `galoisClopen`, and this blueprint id. No exact match. Read
  `Sheaf.AlgebraicGeometry.GaloisComponentPresentation`: its theorem assumes a
  proper normal geometrically reduced variety and constructs an extension and
  selected component, so it does not state this theorem for an already given
  arbitrary integral base and component family. Other hits concern field torsors,
  DVR root covers or unrelated clopen restriction.
- `rg` in Mathlib, both project roots, and `dag/lean_names_upstream.json` for
  `galois_clopen_component_cover`: no declaration-name clash. Blueprint-id search
  in the upstream root also found no existing declaration.

Validation: scompile.py Q27 lem-sfb-galois-clopen-component-cover compiled both
its sandbox and library-module checks cleanly (18.0 s and 7.4 s). No additional
warnings or errors. No node fault or disputed mathematical statement found.

## Second reading by Q27

Read the node's statement again against the complete final theorem signature.
This is a second pass by the assigned worker; no other agents were started,
as required by the dispatcher brief. The maintainer's independent review follows
submission.

Checked the finite, separable, normal hypotheses separately, and checked that
`IsIntegral B` contains precisely the required nonemptiness. Checked that hY
is the scalar-extension square, that U contains actual open subschemes, and
that hcomp, hclosed, hdisjoint and hcover match the entire decomposition. Checked
the inverse in the scalar action and the order of multiplication in `Aut`.
Checked that the coproduct isomorphism is in Over (Spec Ω), that J is nonempty,
and that `∃!` includes freeness, not merely full-group transitivity. Checked all
component pairs i,j, the stabilizer equality, the restriction equation, all
three morphism properties, and both nonempty component lifts and equality of
lifts under H. All equalities are scheme-morphism equalities, so the residue
embeddings have not been discarded. No mismatch found; no statement or signature
change was needed. The proof documentation includes all six DAG steps and names
its dependencies. The withdrawn CompactObject example was followed through its
node to the current upstream module before using its header conventions.
