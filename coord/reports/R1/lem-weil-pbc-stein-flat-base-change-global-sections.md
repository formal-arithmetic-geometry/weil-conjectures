## Worker report

The module Sheaf.AlgebraicGeometry.ProperGlobalSectionsFlatBaseChange states
AlgebraicGeometry.Scheme.Hom.globalSections_flat_base_change, with one sorry and no
new definitions. The node statement is unchanged.

Hypothesis and clause correspondence:

- R and R' are arbitrary commutative rings: `{R S : Type u} [CommRing R] [CommRing S]`.
- The ring map R → R' is `[Algebra R S]`, with map `algebraMap R S`; flatness is
  `[Module.Flat R S]`. This is exactly a flat ring homomorphism, including noninjective maps.
- X and the named proper morphism are `{X : Scheme.{u}}`,
  `(f : X ⟶ Spec (.of R)) [IsProper f]`.
- U is `Spec (.of S)` and X_U is
  `pullback f (Spec.map (CommRingCat.ofHom (algebraMap R S)))`.
- H^0 of the structure sheaf is its ring of global sections `Γ(X, ⊤)`.
  The immediately applied instance lambda equips this ring with precisely
  `((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom.toAlgebra`.
  It adds no hypothesis, independent algebra structure, definition, or let binder.
- The first conjunct asserts existence of a ring equivalence from
  `Γ(X, ⊤) ⊗[R] S` to the global sections of X_U. Its formula for every `a` and `b`
  is pullback along the first projection of a, multiplied by the image of b along
  the second projection after `ΓSpecIso.inv`. Pure tensors additively generate the
  tensor product, so this formula specifies exactly the canonical base-change map;
  existence of this equivalence is equivalent to that map being an isomorphism.
- The final assertion H^0(X,O_X)=R implies H^0(X_U,O)=R' is the second conjunct:
  bijectivity of the original canonical structure ring homomorphism implies
  bijectivity of the new canonical structure ring homomorphism. Equalities here
  mean the canonical identifications, not equality of Lean carrier types.

Dependencies read and used:

- def-weil-proper-morphism: Mathlib.AlgebraicGeometry.Morphisms.Proper,
  AlgebraicGeometry.IsProper. Its full class extends IsSeparated, UniversallyClosed,
  and LocallyOfFiniteType; universally closed also implies QuasiCompact, so this
  is the node's finite-type properness.
- def-pc-scheme-fibre: Mathlib.AlgebraicGeometry.Fiber,
  AlgebraicGeometry.Scheme.Hom.fiber, fiberι and fiberToSpecResidueField were read.
  They are the specialization of Mathlib's pullback and projections to the residue
  field. This statement has an arbitrary affine base change, so it uses their
  underlying general construction, `pullback`, `pullback.fst`, `pullback.snd`, from
  Mathlib.AlgebraicGeometry.Pullbacks; it does not replace arbitrary S by a residue
  field or introduce another fibre definition. The specialized Fiber import is unused
  and therefore omitted.

Source checked: https://stacks.math.columbia.edu/tag/02KH, Lemma 30.5.2, its affine
formula with F=O_X and i=0. Properness supplies qcqs. The module docstring carries
all proof steps of the node, including the final tensor identity. The recorded
proof dependency lem-pc-flat-base-change-cohom is mentioned as the stage-3 route;
its upstream finrankH_pullback record is not used as a substitute for this statement.

Edge cases: the empty scheme gives the zero global-sections ring and zero tensor
product; the conditional final assertion has a false premise unless the base is
also the zero ring. The zero new ring gives an empty base change and zero sections.
Identity base change gives the usual tensor identity. No nonzero ring, field,
Noetherian, connectedness, finite presentation, or reducedness assumption occurs.
All universes and variables are explicit; a common arbitrary universe u is used for
rings and schemes as in Mathlib's scheme pullback API.

Searches:

- msearch.py leansearch: "flat base change global sections scheme": service unavailable,
  Internal Server Error, recorded as unavailable.
- msearch.py leanfinder: "flat base change global sections structure sheaf proper scheme
  tensor product": eight hits, chiefly pullbackSpecIso and pullback-carrier tensor
  results, and flat_appLE; none state proper global-section base change.
- msearch.py loogle: "Algebra.TensorProduct.lift, Scheme.Hom.appTop": no hits,
  Scheme.Hom.appTop was not recognized by the search service.
- msearch.py grep: "flat.*base.*change|base.*change.*global" in AlgebraicGeometry:
  scheme-theoretic dominance stability and flat morphism base-change stability only.
- rg on Mathlib, WeilConjectures, and lean/Sheaf for globalSections_flat_base_change:
  no preexisting declaration of that name. rg for the node id in WeilConjectures:
  no declaration. Concept searches for flatBaseChange, flat_base_change,
  baseChange.*Global, globalSections.*Base, and appTop/tensor found unrelated results,
  ProperFlatGlobalSections (descent of O_S → f_* O_X), and upstream field-specific
  cohomology/finrank material, none the present general ring statement.

Validation: server scompile.py compiled the statement cleanly. Delivery dry run
will additionally check the node signature, formatting and delivery shape.
No statement correction or new node is required.

## Second reading by R1

I independently opened the delivered node, its module, both statement-dependency
nodes and their Mathlib declarations. I read Stacks Tag 02KH and the actual TeX
in coherent.tex, section-cohomology-and-base-change (lines 877ff.) and
lemma-flat-base-change-cohomology (lines 947ff.). The local literature file is
absent, so I retrieved the upstream Stacks TeX into the sandbox. The node's
cohomology.tex filename is an imprecise source pointer: the tag, chapter, lemma
number and prefixed label identify the intended coherent.tex lemma unambiguously.
No mathematical correction is needed. The section assumes schemes and a
quasi-coherent module, not Noetherian schemes or a field. Taking the structure
sheaf and degree zero gives precisely this item; properness supplies qcqs.

Object, hypothesis and conclusion checklist (all verdicts: exact):

1. A commutative ring R: `{R S : Type u} [CommRing R] [CommRing S]` introduces
   R and the node's R-prime (called S). Stacks rings are commutative with identity;
   no nonzero hypothesis is imposed.
2. A scheme X and its named morphism to Spec R: `{X : Scheme.{u}}`
   and `(f : X ⟶ Spec (.of R))`. No affine hypothesis on X is added.
3. Properness of f: `[IsProper f]`. I read Proper.lean:42 and
   UniversallyClosed.lean:167: this is separated, universally closed and locally
   of finite type, with quasi-compactness implied by universally closed. It is
   therefore precisely the finite-type properness of def-weil-proper-morphism,
   not a finiteness or finite-presentation strengthening.
4. A flat ring map R to R-prime: `[Algebra R S] [Module.Flat R S]`, with map
   `algebraMap R S`. Every commutative ring homomorphism supplies this algebra
   structure, including noninjective ones; flatness is flatness of its induced
   module, not faithful flatness. I read Flat.Basic:113 and its arbitrary-universe
   injective-map preservation theorem immediately afterwards.
5. U = Spec R-prime: `Spec (.of S)`, with structure map
   `Spec.map (CommRingCat.ofHom (algebraMap R S))`.
6. X_U = X times_{Spec R} U: `pullback f (Spec.map ...)`. Both projections are
   the categorical `pullback.fst` and `pullback.snd`. I opened Fiber.lean:38--48:
   def-pc-scheme-fibre records the residue-field specialization of precisely this
   construction. This node needs arbitrary affine base change, not a fibre over
   a point; using the underlying existing pullback avoids an incorrect residue-
   field specialization. No dependency module or new notion is missing.
7. H^0(X,O_X): `Γ(X, ⊤)`, global sections of the scheme's structure sheaf.
   The applied lambda installs the algebra structure induced by the actual map
   `((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom.toAlgebra`; it does not assume
   an arbitrary algebra on sections. Scheme.lean:184 gives the contravariant
   section map, and :602--616 identifies the affine section ring with R naturally.
8. The canonical comparison is an isomorphism: `∃ e : Γ(X, ⊤) ⊗[R] S ≃+* Γ(..., ⊤)`
   with the following `∀ a b` clause. The image of each pure tensor is exactly
   `(pullback.fst ...).appTop a` times the image of b under the second projection
   after `ΓSpecIso.inv`. These pure tensors generate the tensor product additively,
   so the formula specifies the canonical comparison uniquely; an arbitrary
   abstract ring equivalence would not suffice. Its formula also ensures the
   natural S-algebra compatibility. No conclusion is weakened or strengthened.
9. In particular, H^0(X,O_X)=R implies H^0(X_U,O)=R-prime: the second conjunct
   is `Function.Bijective` of the original canonical structure ring map implying
   `Function.Bijective` of the new one. These are exactly the canonical
   identifications intended by the node's equalities, rather than arbitrary
   abstract isomorphisms. The universal data precede both conclusions; the
   original bijectivity is not a hypothesis of the first conclusion.

Edge cases: X may be empty, yielding the zero section ring and zero tensor
product. Its final premise can hold only for a zero base ring. S may be the zero
ring (a flat module), giving the empty pullback and zero sections. A zero R forces
S and any X over Spec R to be empty/zero as appropriate. Identity base change
has the ordinary tensor identity. No index set is quantified, and i=0 is the
specialization itself, so there is no hidden positive-degree case. All
characteristics are allowed. The arbitrary common universe u is the universe of
Mathlib's Scheme pullback API; objects from different sizes can be lifted to a
common larger universe. No independent smaller test universe makes a hypothesis
vacuous, and every binder/universe is bound explicitly.

Independent searches, with queries different from the first reader:

- LeanFinder via msearch.py: "Tensor extension of scalars commutes with regular
  functions on a quasi compact separated scheme". Eight hits: pullback-carrier
  tensor formulas and pullbackSpecIso_hom_base_assoc; no declaration of this node.
- Loogle via msearch.py: `"appTop", "Flat"`. One hit, Scheme.Hom.flat_appTop,
  concerns flatness of the section map between affine schemes, not this theorem.
- Mathlib grep via msearch.py: `sections.*tensor|tensor.*sections|cohomology.*flat|
  flat.*cohomology`, under AlgebraicGeometry: no hits.
- Direct rg with the same conceptual terms and global/base-change variants on
  WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json. I opened the hits
  WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.GlobalSections,
  WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent,
  WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks, and the project's
  ProperFlatGlobalSections.lean.

The important extra finding is `AlgebraicGeometry.isPushout_appTop_of_flat` in
EtaleTopologicalInvariance.GlobalSections: it states the section-ring pushout for
an arbitrary qcqs X and affine flat base map. Its separate `IsPushout.tensorEquiv`
and `tensorEquiv_tmul` give a useful stage-3 proof route. It does not have this
node's hypotheses and full conclusion (in particular its conditional final
clause), so it is not an exact existing declaration to attach instead. No new
definition is introduced here, and this proper specialization with its corollary
is not a duplicate definition. ProperFlatGlobalSections assumes f itself flat,
finite presentation and geometrically reduced/connected fibres and states
universal structure-sheaf pushforward: it is a different theorem. The generic
proof dependency's recorded finrankH_pullback is only field-specific dimension
invariance, so it is not a replacement statement for this ring-level theorem;
the delivered module does not use it as such.

I found no mathematical mismatch and changed neither the Lean nor its recorded
signature. I supplemented the search audit with the upstream pushout theorem,
corrected the source-file location in this reading, and appended this complete
review. There are no new nodes, dependency modules, statement_change records,
hollow definitions, private notions, file-local notation or proofs. The sole
proof remains `sorry`. Both docstrings identify the tag and blueprint; the theorem
docstring follows the node's proof: qcqs, flat cohomology base change, structure-
sheaf pullback, canonical comparison, and the tensor identity for the corollary.
All imports contribute the proper, pullback/tensor and flat-module APIs.

Validation after second reading: scompile.py compiled the unchanged module on the
server in 1.9 seconds, exit code 0, without warnings. deliver2.py --no-push printed
OK: preflight passed and the module compiled. The node's lean.statement remains
verbatim the file signature, as checked by that preflight.

## Stage-2 review by R-sfb (FIX)

The delivered statement gave Γ(X, ⊤) its R-algebra structure through an applied instance
lambda `(fun [instΓ : Algebra R Γ(X, ⊤)] => …) (instΓ := (…).hom.toAlgebra)`, which the
STATE lines REGULAR RING MAPS and FLAT RING MAPS forbid (never an applied instance lambda or
`RingHom.toAlgebra` inline), and spelled the canonical map as an untied `∃ e : … ≃+* …` with a
pure-tensor formula. The reviewer restated the first conclusion in the canonical form already
used in the project (slopmaster2 `isPushout_appTop_of_flat`, landed
QuasiCoherentAlgebraAffineInclusion): `IsPushout f.appTop (Spec.map φ).appTop
(pullback.fst f _).appTop (pullback.snd f _).appTop` in `CommRingCat`, which says exactly
that the canonical map Γ(X) ⊗_{Γ(Spec R)} Γ(Spec S) → Γ(X_U) is an isomorphism. The
corollary is stated with `IsIso ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop)` as in landed
ProperNormalizedFibres. Hypotheses unchanged; the node statement unchanged.
