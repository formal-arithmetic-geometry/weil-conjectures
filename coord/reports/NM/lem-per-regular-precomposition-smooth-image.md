## Worker report

The module `Sheaf.AlgebraicGeometry.RegularPrecompositionSmoothImage` states
`AlgebraicGeometry.exists_open_smooth_of_regular_precomposition`, with one postponed proof
(`sorry`). It introduces no definitions, extra nodes, or dependency repairs. The original
node is unchanged except for its `lean` record.

Clause-by-clause correspondence:

- The schemes Z, T, S are `{Z T S : Scheme.{u}}`, with arbitrary explicit universe u.
- Their local Noetherianity is `[IsLocallyNoetherian Z] [IsLocallyNoetherian T]
  [IsLocallyNoetherian S]`.
- The two morphisms are `(p : Z ⟶ T) (g : T ⟶ S)`.
- Regularity of p is `(hp : IsRegularSchemeMorphism p)`.
- Local finite presentation of g is `[LocallyOfFinitePresentation g]`.
- Regularity of g composed with p is `(hcomp : IsRegularSchemeMorphism (p ≫ g))`;
  Lean's categorical composition order is first p, then g.
- The open subscheme is `∃ W : T.Opens`; Mathlib's `W.toScheme` is the open restriction,
  and `W.ι` is its canonical inclusion in T.
- Containment of the set-theoretic image is `(∀ z : Z, p z ∈ W)`. This is equivalent
  to containment of `Set.range p`, with no surjectivity assumption.
- Smoothness of the restriction is `Smooth (W.ι ≫ g)`.
- There is no hypothesis of surjectivity or finite presentation of p.

Recorded dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.RegularSchemeMorphism`:
  `AlgebraicGeometry.IsRegularSchemeMorphism`, flat with geometrically regular fibres
  tested after finite extensions of residue fields in the scheme universe.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- The canonical open inclusion was read in `Mathlib.AlgebraicGeometry.Restrict`:
  `Scheme.Opens.toScheme` and `Scheme.Opens.ι`.

Proof-only imports follow the recorded, already stated proof dependencies:
`Mathlib.Geometry.RingedSpace.LocallyRingedSpace` (`LocallyRingedSpace.Hom` and its
stalk maps), `WeilConjectures.RingTheory.GRing` (`RingHom.IsRegular`),
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`
(`Module.FaithfullyFlat.of_flat_of_isLocalHom` and spectral surjectivity), and
`WeilConjectures.RingTheory.RegularPermanence`
(`RingHom.isRegular_of_isRegular_comp`). The proof dependencies
`lem-per-regular-scheme-stalk-criterion` and
`lem-per-lfp-regular-stalk-smooth-neighborhood` currently have no recorded Lean declarations;
they are named in the proof docstring but are not imported. They are not needed to TYPE this
statement. No missing notion is concealed by a new assumption.

Source check: opened Temkin's paper at
https://math.huji.ac.il/~temkin/papers/Non_Embedded_Desingularization.pdf and read
Lemma 2.1.4(ii), printed p.8, and its use in Proposition 3.3.5, printed p.25.
The local cancellation lemma applies at each point of the image, and the proposition
uses a smooth open containing that image. The docstring retains all four DAG proof
steps and their dependency identifiers. No statement correction or dispute was found.

Edge cases checked before writing: if Z is empty, the image condition is vacuous and
W may be empty, whose morphism is smooth. If T is empty then Z is empty as well.
For p the identity, the statement reduces to smoothness of an lfp regular morphism.
For a nonsurjective open immersion p it asserts smoothness only near its image, allowing
singularities elsewhere. Infinite non-finitely-presented regular maps p remain allowed.
Over imperfect fields the hypotheses retain geometric regularity, rather than ordinary
regularity; no perfectness or characteristic restriction is inserted. All schemes share
an arbitrary universe, as required by the recorded regular-morphism interface.

Searches for an existing statement (full wrapper output is in searches.jsonl):

- msearch leanfinder: "A locally finitely presented morphism of locally Noetherian schemes
  is smooth on an open containing the image of a regular morphism if their composite is
  regular". Eight hits, about smoothness, composition and lfp; no matching statement.
- msearch loogle: "AlgebraicGeometry.Smooth, AlgebraicGeometry.LocallyOfFinitePresentation".
  Three hits: smooth implies lfp, smooth locus equals top, and smoothness from flatness
  and smooth fibres; none states regular precomposition detection near its image.
- msearch grep: "regular.*(precomp|permanence|stalk)|smooth.*regular", restricted to
  AlgebraicGeometry. Zero hits.
- msearch leansearch: "If p is a regular morphism of locally Noetherian schemes and g is
  locally of finite presentation and g composed with p is regular, g is smooth near the
  image of p". Eight hits on smoothness definitions and smooth implies lfp; no match.
- rg in both `lean/WeilConjectures` and `lean/Sheaf` for regular/precomposition/smooth/image
  combinations found smooth-over-field regularity and unrelated regular module results,
  not this statement. The exact item id had no upstream source occurrence. Exact proposed
  declaration-name searches, including `dag/lean_names_upstream.json`, had no matches.

Validation: scompile.py compiled the delivered file in sandbox and library module modes
successfully (1.6 s and 1.5 s), with no compiler messages. `autoImplicit` and
`relaxedAutoImplicit` are false. Every theorem proof is exactly `by sorry`.

## Second reading by NM

The dispatcher explicitly prohibits starting other agents and assigns the independent review
to the maintainer. This section records a separate self-check, not an independent reader.
Reopened the node and generated Lean signature: all three local Noetherian hypotheses,
the regular p hypothesis, the lfp g hypothesis, and the regular composite hypothesis match.
The existential ranges over every open of T; its image clause quantifies over every z of Z;
the smoothness clause uses the canonical inclusion composed with g in the correct order.
No condition on p beyond regularity was added. No data was chosen or left as sorry.
The empty case is included. No mismatch or change was found in this rereading.
