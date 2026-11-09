# CLAUDE.md — conventions for all agent sessions in this repo

- UK English. AsciiDoc for docs (`.adoc`), not Markdown (this file and
  the bootstrap prompt are the only exceptions).
- GitHub is the single source of truth; mirrors are spokes.
- No Python. Shell for glue; Podman if containers are ever needed.
- Proofs follow the estate policy (`hyperpolymath/standards`
  `3-practice/PROOF-POLICY.adoc`): marches is *theory*, so Agda is the
  source of truth, rechecked in Rocq and Lean, with no Mathlib. The
  Lean 4 development here predates that ruling and is target-only
  evidence (the Lean leg) until an Agda proof of the same statement is
  checked and the two are reconciled. Every theorem is `ungraded`
  (no PWG) until then; `PROOF-STATUS.adoc` holds the record. Never call
  a theorem graded or "verified" under the estate policy on the
  strength of the Lean build alone.
- Claim taxonomy: PROVEN / TESTED / ASSUMED / DESIGNED / OPEN.
  Anti-Goodhart clause: a status upgrade must name the transcribable
  artifact that discharges it (build log, eval output, test run).
  Never fabricate identifiers, file contents, or citations.
- Scope discipline: one ROADMAP rung per session. No new features
  outside the rung. No convergence overclaims — agda-routing owns
  that ground (see LIMITATIONS.adoc).
- If a file from the wider estate is needed (e.g. TropicalAdapterPath.lean),
  obtain the real file; never reconstruct it from memory.
- Before ending a session: update STATE.adoc, commit with a message
  naming the rung, and tag only if all gates pass.
- Gates for this repo: `lake build` green; `grep -rn "sorry" Marches/`
  empty; the BadGadget `#eval` prints the period-2 orbit. A change that
  adds or alters a theorem also updates `PROOF-STATUS.adoc`.
