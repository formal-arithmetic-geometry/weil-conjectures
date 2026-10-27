## Worker report

Stage 2: stated `AlgebraicGeometry.AlgebraicSpace.exists_finite_affine_fppf_refinement`
in `lean/Sheaf/AlgebraicGeometry/AlgebraicSpaceFppfFiniteAffineRefinement.lean`.
One theorem, its proof `sorry`; no definitions, new nodes, dependency modules or
new Mathlib leaves. The item changes only in its `lean` record and addition of the
landed definition owner `def-sfb-space-morphism-properties` to `stmt_deps`.
The accepted stage-1 statement, split, sources and review remain unchanged.

The resume message explicitly assigns stage 2 and coord/queue.tsv confirms stage 2.
The original sandbox held only brief markers: no delivery or compile was interrupted.
The live node already has Q41's accepted stage-1 split, but no Lean record. I followed
the stage-2 brief's maintenance handoff and preserved that split. The dispatcher's
WEIL_SANDBOX setting directed msearch.py's real logs into the stage-2 sandbox;
searches.jsonl here is an unchanged copy of those actual search records. The Lean
module, node and report are in the sandbox specified by the original brief.

Hypothesis-by-hypothesis rendering:

- `S : Scheme.{u}`, `Y : AlgebraicSpace S`, `Yᵢ : I → AlgebraicSpace S`, and
  `q : ∀ i, Yᵢ i ⟶ Y` give the family over S. `I : Type w` is an arbitrary index
  universe, with no finiteness or nonemptiness assumption on the input family.
- `hflat` and `hlfp` use `MapIsFlat` and `MapIsLocallyOfFinitePresentation` from
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`. I read their
  definitions: they test the scheme predicate on every compatible pair of
  representable etale scheme charts. Their already landed owning definition node
  is the one addition to stmt_deps. No private predicate is introduced.
- `hsurj` uses `IsJointlySurjective` from
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity` on `(q i).hom.hom`.
  Its definition permits a field extension before lifting each field-valued point,
  exactly as the point-class convention requires, rather than demanding a lift
  over the original field.
- `T : Over S`, `[IsAffine T.left]`, and `t : yoneda.obj T ⟶ Y.obj.obj` give the
  arbitrary affine S-scheme and map. There is no representability assumption on
  q or t, and no quasi-compactness, separation or Noetherian hypothesis is added.

Clause-by-clause conclusion:

- `n : ℕ` and `a : Fin n → I` give the finite labelled set J. `V : Fin n → Over S`
  and `∀ j, IsAffine (V j).left` give affine schemes over S. `p j : V j ⟶ T` is an
  S-map; `r j` is a natural transformation from the Yoneda functor of that SAME
  S-scheme to the presheaf of `Yᵢ (a j)`.
- `r j ≫ (q (a j)).hom.hom = yoneda.map (p j) ≫ t` gives precisely
  q_a(j) r_j = t p_j, with Lean composition ordered left to right.
- `Flat (p j).left ∧ LocallyOfFinitePresentation (p j).left` gives both local
  properties. `∀ x, ∃ j v, (p j).left.base v = x` is the topological union of
  images condition on T.
- `∐ fun j ↦ (V j).left` is Mathlib's actual scheme coproduct from
  Mathlib.AlgebraicGeometry.Limits. The induced map is always the SAME term
  `Sigma.desc (fun j ↦ (p j).left)`. The conclusions state affineness of this
  coproduct and flatness, surjectivity and local finite presentation of that map.
- Membership of its `Presieve.singleton` in Scheme.fppfPrecoverage and in
  Scheme.fpqcPrecoverage gives exactly the two singleton covering conclusions,
  using the existing predicates of def-pc-fppf-site and def-weil-pbc-fpqc-covering.

Read dependency interfaces at their recorded sources: Scheme/Hom and IsAffine;
AlgebraicSpace's full subcategory and representable-test/atlas definitions;
IsJointlySurjective's explicit field-extension condition; MapIsLocally and its
flat/lfp specializations; the Mathlib Flat, LocallyOfFinitePresentation and
Surjective classes; the small discrete scheme colimit instance and Sigma.desc;
and fppfPrecoverage/fpqcPrecoverage. The size convention is metatheoretic and is
rendered by u,w universe parameters, not a hollow binder. Public imports expose
the statement predicates; plain imports are the recorded scheme affine-refinement
and scheme-etale-locality proof modules. Space fibre products are already imported
by the chartwise-properties module. Finite affine coproduct, open-immersion-etale
and fppf-to-fpqc leaves are in the imported Mathlib modules. The accepted proof's
lem-sfb-space-fppf-covering-calculus has no Lean record yet, so no module can be
imported for it; its proof use is preserved in the theorem docstring for stage 3.
That theorem is not needed to elaborate this statement.

Read source: literature/stacks-project/spaces-topologies.tex, Tag 0DFQ,
lemma-zariski-etale-smooth-syntomic-fppf-fpqc, proof at lines 1267-1300. It forms
affine etale charts of V times_U U_i; their composites are flat and locally of
finite presentation, hence open; affine quasi-compactness selects finitely many.
The accepted split packages them by the finite scheme coproduct. Read the scheme
Tag 021P declaration and Mathlib Fpqc.lean:38-73, including Tag 022C's comparison.
No SGA source or statement correction is involved.

Edge cases: n may be zero, so empty T admits the empty selection, with coproduct
Spec 0 and all pointwise/factorization conditions vacuous. An empty input I forces
Y, and then every scheme test, empty; no Nonempty I binder excludes this case.
Empty members, repeated labels, identity singleton, non-quasi-compact members and
arbitrary S are all allowed. The p_j only need to be flat and locally finitely
presented; no etaleness requirement has been accidentally added.

Searched for existing statements in Mathlib and both project trees. The upstream
Scheme.exists_finite_fppf_affine_open_refinement at Fpqc.lean:189, and the recorded
scheme proof dependency, apply only to families of schemes, not algebraic-space
sources. No upstream AlgebraicSpace occurrence or exact statement was found.
The new declaration name/module were absent. The msearch hits were read: they
concern scheme affine covers, scheme flat/lfp predicates, the fppf precoverage,
and finite-coproduct spectra, none an exact match for this item. Actual queries:

- `grep`: AlgebraicSpace|finite.*fppf.*refin|fppf.*affine — 0 hits; .
- `leansearch`: An algebraic space fppf cover has a finite affine scheme refinement over each affine scheme mapping to its target — 8 hits; AlgebraicGeometry.Scheme.AffineCover.covers, AlgebraicGeometry.Scheme.affineCover, AlgebraicGeometry.ExistsHomHomCompEqCompAux.𝒰D, AlgebraicGeometry.Scheme.AffineCover.ctorIdx, AlgebraicGeometry.Scheme.OpenCover.affineRefinement, AlgebraicGeometry.Scheme.AffineCover.J, AlgebraicGeometry.Scheme.AffineCover.f, AlgebraicGeometry.Scheme.directedAffineCover.
- `loogle`: "fppf", "refinement" — 0 hits; .
- `leanfinder`: Every fppf covering family of algebraic spaces admits a finite affine scheme refinement over an affine test scheme — 8 hits; AlgebraicGeometry.ExistsHomHomCompEqCompAux.h𝒰X, AlgebraicGeometry.Scheme.AffineCover, AlgebraicGeometry.ExistsHomHomCompEqCompAux.h𝒰S, AlgebraicGeometry.ExistsHomHomCompEqCompAux.𝒰D, AlgebraicGeometry.Scheme.OpenCover.affineRefinement, AlgebraicGeometry.instIsAffineXSchemeAffineCover, AlgebraicGeometry.ExistsHomHomCompEqCompAux.𝒰D₀, AlgebraicGeometry.Scheme.AffineCover.J.
- `grep`: fppfPrecoverage|sigmaSpec|affineRefinement — 25 hits; Mathlib/AlgebraicGeometry/Limits.lean, Mathlib/AlgebraicGeometry/Limits.lean, Mathlib/AlgebraicGeometry/Limits.lean, Mathlib/AlgebraicGeometry/Limits.lean, Mathlib/AlgebraicGeometry/Limits.lean, Mathlib/AlgebraicGeometry/Cover/Open.lean, Mathlib/AlgebraicGeometry/Cover/Open.lean, Mathlib/AlgebraicGeometry/Cover/Open.lean.
- `leanfinder`: A jointly surjective flat locally finitely presented family with algebraic space sources can be refined by finitely many affine schemes and their affine coproduct — 8 hits; AlgebraicGeometry.LocallyOfFinitePresentation, AlgebraicGeometry.instDescendsAlongSchemeMinMorphismPropertySurjectiveFlatLocallyOfFinitePresentationOfQuasiCompactOfIsZariskiLocalAtTarget, AlgebraicGeometry.ExistsHomHomCompEqCompAux.h𝒰S, AlgebraicGeometry.ExistsHomHomCompEqCompAux.𝒰D, AlgebraicGeometry.Scheme.AffineCover, AlgebraicGeometry.Flat.surjective_descendsAlong_surjective_inf_flat_inf_quasicompact, AlgebraicGeometry.ExistsHomHomCompEqCompAux.h𝒰X, AlgebraicGeometry.UniversallyOpen.of_flat.

Validation: scompile.py compiled the sandbox and library module cleanly on the
server (15.1 s and 5.1 s respectively, within the default 60 s limit). No local
build or Lake command was run. The signature is recorded verbatim, with whitespace
normalized, in lean.statement. A premature dry run failed only because report.md
was not yet written after locating the search log; no commit or push resulted.

## Review by Q51

I compared the accepted statement and source with the Lean file, binder by binder
and conjunct by conjunct. The S-structures on V_j used by r_j and p_j are shared;
the commutative-square equation has the right direction. Each concluding property
uses the identical canonical Sigma.desc term, so no unrelated singleton cover can
satisfy those conclusions. The flat/lfp hypotheses use the already landed chart
predicates, with their definition owner added to stmt_deps. Joint surjectivity is
the field-extension condition, and there is no stronger fixed-field lifting
assumption. Fin n admits the empty choice, and there is no extra nonempty or
quasi-compact/separated hypothesis. I found no statement correction necessary.

The docstring carries the four accepted proof steps with their dependency ids and
sources. The module has just one postponed theorem and no hollow data. I checked
the module header, exposed section, public statement imports, plain proof imports,
namespace, autoImplicit false and 100-character line limit. This is my own review,
not an independent second reading; the maintainer supplies independent review.

## Second reading by Q51

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
