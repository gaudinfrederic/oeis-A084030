import A084029Table

open A084029

set_option maxRecDepth 100000 in
set_option maxHeartbeats 60000000 in
/-- Certificat partiel (haut-ter, quart 2) de la table `table029` :
    pour chaque n ∈ [105,113], la liste `table029 n` a n éléments
    distincts, chacun multiple de n à n chiffres de somme n.
    Re-decoupage de `cert_hi2` [98,130] (timeout whnf 60M) :
    quarts [98,104]/[105,113]/[114,121]/[122,130]. -/
theorem cert_hi2b :
    ∀ n ∈ Finset.Icc 105 113,
      n ≤ (table029 n).length ∧ (table029 n).Nodup ∧
        ∀ N ∈ table029 n,
          n ∣ N ∧ (Nat.digits 10 N).length = n ∧
            (Nat.digits 10 N).sum = n := by
  intro n hn
  rw [Finset.mem_Icc] at hn
  obtain ⟨h_lo, h_hi⟩ := hn
  interval_cases n <;> decide +kernel
